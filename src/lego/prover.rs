use std::ops::Mul;

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, Group, VariableBaseMSM};
use ark_ff::{Field, PrimeField, UniformRand, Zero};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
};
use ark_std::{cfg_into_iter, cfg_iter, end_timer, rand::Rng, start_timer, vec, vec::Vec};
use blake2::{Blake2b, Digest};
use rayon::prelude::*;

use super::{
    link::{PESubspaceSnark, SubspaceSnark},
    r1cs_to_qap::{LibsnarkReduction, R1CStoQAP},
    Proof, ProofWithLink, ProvingKeyWithLink,
};

macro_rules! to_bytes {
    ($data:expr) => {{
        use ark_serialize::CanonicalSerialize;
        let mut serialized = vec![0; $data.compressed_size()];
        $data.serialize_compressed(&mut serialized[..]).unwrap();
        serialized
    }};
}

#[inline]
pub fn create_random_proof_incl_cp_link<E, C, R>(
    circuit: C,
    v: E::ScalarField,
    link_v: &[E::ScalarField],
    pk: &ProvingKeyWithLink<E>,
    rng: &mut R,
) -> Result<ProofWithLink<E>, SynthesisError>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
    R: Rng,
{
    let r = E::ScalarField::rand(rng);
    let s = E::ScalarField::rand(rng);
    let zeta = E::ScalarField::rand(rng);
    assert!(!zeta.is_zero());

    let prover_time = start_timer!(|| "Groth16::Prover");
    let (cs, h) = synthesize_circuit::<E, C, LibsnarkReduction>(circuit)?;

    let ConstraintSystem { instance_assignment, mut witness_assignment, .. } =
        cs.into_inner().unwrap();

    let pk_common = &pk.common;
    let vk = &pk.vk.groth16_vk;

    let uncommitted_w = witness_assignment.split_off(vk.commit_witness_count);
    let committed_w_bn: Vec<_> = witness_assignment.into_par_iter().map(|s| s.into()).collect();

    let c_acc_time = start_timer!(|| "Compute C");

    let v_repr = v.into_bigint();

    // Compute C
    let delta_prime_g1 = pk_common.delta_g1.mul(zeta).into_affine();
    let delta_prime_g2 = vk.delta_g2.mul(zeta).into_affine();

    let v_eta_delta_inv = pk_common.eta_delta_inv_g1.mul_bigint(v_repr);

    end_timer!(c_acc_time);

    // Compute D
    let d_acc_time = start_timer!(|| "Compute D");
    let g_d = E::G1::msm_bigint(&vk.gamma_abc_g1[instance_assignment.len()..], &committed_w_bn)
        + vk.eta_gamma_inv_g1.mul_bigint(v_repr);
    end_timer!(d_acc_time);

    let r_repr = r.into_bigint();
    let s_repr = s.into_bigint();
    let rs_repr = (r * s).into_bigint();

    let mut assignment =
        instance_assignment.into_par_iter().skip(1).map(|s| s.into_bigint()).collect::<Vec<_>>();
    assignment.extend_from_slice(&committed_w_bn);
    assignment.extend(uncommitted_w.par_iter().map(|s| s.into_bigint()).collect::<Vec<_>>());

    // Compute A
    let a_acc_time = start_timer!(|| "Compute A");
    let r_g1 = delta_prime_g1.mul_bigint(r_repr);
    let g_a = calculate_coeff(r_g1, &pk_common.a_query, vk.alpha_g1, &assignment);
    end_timer!(a_acc_time);

    // Compute B in G1
    let b_g1_acc_time = start_timer!(|| "Compute B in G1");
    let s_g1 = delta_prime_g1.mul_bigint(s_repr);
    let g1_b = calculate_coeff(s_g1, &pk_common.b_g1_query, pk_common.beta_g1, &assignment);
    end_timer!(b_g1_acc_time);

    // Compute B in G2
    let b_g2_acc_time = start_timer!(|| "Compute B in G2");
    let s_g2 = delta_prime_g2.mul_bigint(s_repr);
    let g2_b = calculate_coeff(s_g2, &pk_common.b_g2_query, vk.beta_g2, &assignment);
    end_timer!(b_g2_acc_time);

    drop(assignment);

    let c_time = start_timer!(|| "Finish C");

    let hash = Blake2b::new()
        .chain(to_bytes!(&g_a.into_affine()))
        .chain(to_bytes!(&g2_b.into_affine()))
        .chain(to_bytes!(&delta_prime_g2));
    let m_fr = E::ScalarField::from_le_bytes_mod_order(&hash.finalize());
    let zeta_m_inv = (zeta + m_fr).inverse().unwrap();
    let factor = (zeta * zeta_m_inv).into_bigint();

    let h_assignment = cfg_into_iter!(h).map(|s| (s * zeta_m_inv).into()).collect::<Vec<_>>();
    let h_acc = E::G1::msm_bigint(&pk_common.h_query, &h_assignment);
    let aux_assignment_unscaled =
        uncommitted_w.into_par_iter().map(|s| (s * zeta_m_inv).into()).collect::<Vec<_>>();

    let l_aux_acc = E::G1::msm_bigint(&pk_common.l_query, &aux_assignment_unscaled);

    let mut g_c = g_a.mul_bigint(s_repr).mul_bigint(factor);
    g_c += &g1_b.mul_bigint(r_repr).mul_bigint(factor);
    g_c -= &delta_prime_g1.mul_bigint(rs_repr).mul_bigint(factor);
    g_c += &l_aux_acc;
    g_c += &h_acc;
    g_c -= &v_eta_delta_inv.mul_bigint(zeta_m_inv.into_bigint());
    end_timer!(c_time);

    let proof = Proof {
        a: g_a.into_affine(),
        b: g2_b.into_affine(),
        c: g_c.into_affine(),
        d: g_d.into_affine(),
        delta_prime: delta_prime_g2,
    };

    let link_v_bn = link_v.par_iter().map(|s| s.into_bigint()).collect::<Vec<_>>();

    let g_d_link = cfg_iter!(link_v_bn)
        .zip_eq(&committed_w_bn)
        .map(|(v, w)| pk.vk.link_bases.0.mul_bigint(w) + pk.vk.link_bases.1.mul_bigint(v))
        .collect::<Vec<_>>();
    let g_d_link = E::G1::normalize_batch(&g_d_link);

    let link_pi = {
        let link_time = start_timer!(|| "Compute CP_{link}");
        let link_pi = PESubspaceSnark::<E>::prove(
            &pk.vk.link_pp,
            &pk.link_ek,
            &[committed_w_bn, link_v_bn, vec![v.into_bigint()]].concat(),
        );

        end_timer!(link_time);
        link_pi
    };

    end_timer!(prover_time);

    Ok(ProofWithLink { groth16_proof: proof, link_d: g_d_link, link_pi })
}

/// Given a circuit, generate its constraints and the corresponding QAP witness.
#[inline]
pub fn synthesize_circuit<E, C, QAP>(
    circuit: C,
) -> Result<(ConstraintSystemRef<E::ScalarField>, Vec<E::ScalarField>), SynthesisError>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
    QAP: R1CStoQAP,
{
    let cs = ConstraintSystem::new_ref();

    // Set the optimization goal
    cs.set_optimization_goal(OptimizationGoal::Constraints);

    // Synthesize the circuit.
    let synthesis_time = start_timer!(|| "Constraint synthesis");
    circuit.generate_constraints(cs.clone())?;
    if !cs.is_satisfied()? {
        return Err(SynthesisError::Unsatisfiable);
    }
    end_timer!(synthesis_time);

    let lc_time = start_timer!(|| "Inlining LCs");
    cs.finalize();
    end_timer!(lc_time);

    let witness_map_time = start_timer!(|| "R1CS to QAP witness map");
    let h = QAP::witness_map::<_, GeneralEvaluationDomain<_>>(cs.clone())?;
    end_timer!(witness_map_time);
    Ok((cs, h))
}

fn calculate_coeff<G: CurveGroup>(
    initial: G,
    query: &[G::Affine],
    vk_param: G::Affine,
    assignment: &[<G::ScalarField as PrimeField>::BigInt],
) -> G {
    let el = query[0];
    let acc = G::msm_bigint(&query[1..], assignment);

    let mut res = initial;
    res += &el;
    res += &acc;
    res += &vk_param;

    res
}
