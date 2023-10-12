use std::ops::Mul;

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, Group, VariableBaseMSM};
use ark_ff::{PrimeField, UniformRand, Zero};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
};
use ark_std::{cfg_into_iter, cfg_iter, end_timer, rand::Rng, start_timer, vec, vec::Vec};
use rayon::prelude::*;

use super::{
    link::{PESubspaceSnark, SubspaceSnark},
    r1cs_to_qap::{LibsnarkReduction, R1CStoQAP},
    Proof, ProofWithLink, ProvingKeyCommon, ProvingKeyWithLink, VerifyingKey,
};

/// Same as `create_random_proof` but returns the CP_link and its corresponding proof as well. `link_v`
/// is the blinding in CP_link
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

    create_proof_incl_cp_link::<E, C>(circuit, pk, r, s, v, link_v)
}

#[inline]
/// Create a LegoGroth16 proof using randomness `r`, `s`, `v` and `link_v` where `v` is the blinding in
/// the witness commitment in proof and `link_v` is the blinding in the witness commitment in CP_link
pub fn create_proof_incl_cp_link<E, C>(
    circuit: C,
    pk: &ProvingKeyWithLink<E>,
    r: E::ScalarField,
    s: E::ScalarField,
    v: E::ScalarField,
    link_v: &[E::ScalarField],
) -> Result<ProofWithLink<E>, SynthesisError>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
{
    create_proof_incl_cp_link_with_reduction::<E, C, LibsnarkReduction>(
        circuit, pk, r, s, v, link_v,
    )
}

/// Create a LegoGroth16 proof using randomness `r` and `s`.
/// `v` is the randomness of the commitment `proof.d` and `link_v` is the randomness to CP_link commitment
#[inline]
pub fn create_proof_incl_cp_link_with_reduction<E, C, QAP>(
    circuit: C,
    pk: &ProvingKeyWithLink<E>,
    r: E::ScalarField,
    s: E::ScalarField,
    v: E::ScalarField,
    link_v: &[E::ScalarField],
) -> Result<ProofWithLink<E>, SynthesisError>
where
    E: Pairing,
    C: ConstraintSynthesizer<E::ScalarField>,
    QAP: R1CStoQAP,
{
    let prover_time = start_timer!(|| "Groth16::Prover");
    let (cs, h) = synthesize_circuit::<E, C, QAP>(circuit)?;

    let prover = cs.borrow().unwrap();
    let proof = create_proof_incl_cp_link_with_assignment::<E, QAP>(
        pk,
        r,
        s,
        v,
        link_v,
        &h,
        &prover.instance_assignment,
        &prover.witness_assignment,
    )?;

    drop(prover);
    drop(cs);

    end_timer!(prover_time);

    Ok(proof)
}

/// Create the proof including CP_link and its corresponding proof given the public and private input assignments
#[inline]
fn create_proof_incl_cp_link_with_assignment<E, QAP>(
    pk: &ProvingKeyWithLink<E>,
    r: E::ScalarField,
    s: E::ScalarField,
    v: E::ScalarField,
    link_v: &[E::ScalarField],
    h: &[E::ScalarField],
    input_assignment: &[E::ScalarField],
    witness_assignment: &[E::ScalarField],
) -> Result<ProofWithLink<E>, SynthesisError>
where
    E: Pairing,
    QAP: R1CStoQAP,
{
    let (proof, comm_wits) = create_proof_and_committed_witnesses_with_assignment::<E, QAP>(
        &pk.common,
        &pk.vk.groth16_vk,
        r,
        s,
        v,
        &h,
        input_assignment,
        witness_assignment,
    )?;

    let g_d_link = cfg_iter!(link_v)
        .zip_eq(&comm_wits)
        .map(|(v, w)| (pk.vk.link_bases.0.mul(*w) + pk.vk.link_bases.1.mul(*v)).into_affine())
        .collect();

    let mut ss_snark_witness = comm_wits;
    ss_snark_witness.extend_from_slice(link_v);
    ss_snark_witness.push(v);

    let link_time = start_timer!(|| "Compute CP_{link}");
    let link_pi = PESubspaceSnark::<E>::prove(&pk.vk.link_pp, &pk.link_ek, &ss_snark_witness);

    end_timer!(link_time);

    drop(ss_snark_witness);

    Ok(ProofWithLink { groth16_proof: proof, link_d: g_d_link, link_pi })
}

/// Returns the proof and the committed witnesses.
#[inline]
fn create_proof_and_committed_witnesses_with_assignment<E, QAP>(
    pk_common: &ProvingKeyCommon<E>,
    vk: &VerifyingKey<E>,
    r: E::ScalarField,
    s: E::ScalarField,
    v: E::ScalarField,
    h: &[E::ScalarField],
    input_assignment: &[E::ScalarField],
    witness_assignment: &[E::ScalarField],
) -> Result<(Proof<E>, Vec<E::ScalarField>), SynthesisError>
where
    E: Pairing,
    QAP: R1CStoQAP,
{
    let h_assignment = cfg_into_iter!(h).map(|s| s.into_bigint()).collect::<Vec<_>>();
    let c_acc_time = start_timer!(|| "Compute C");

    let h_acc = E::G1::msm_bigint(&pk_common.h_query, &h_assignment);
    drop(h_assignment);

    let v_repr = v.into_bigint();

    // Compute C
    let aux_assignment = cfg_iter!(witness_assignment).map(|s| s.into_bigint()).collect::<Vec<_>>();

    let committed_witnesses = &aux_assignment[..vk.commit_witness_count];
    let uncommitted_witnesses = &aux_assignment[vk.commit_witness_count..];

    let l_aux_acc = E::G1::msm_bigint(&pk_common.l_query, uncommitted_witnesses);

    let v_eta_delta_inv = pk_common.eta_delta_inv_g1.into_group().mul_bigint(v_repr);

    end_timer!(c_acc_time);

    let r_repr = r.into_bigint();
    let s_repr = s.into_bigint();
    let rs_repr = (r * s).into_bigint();
    let delta_g1_proj = pk_common.delta_g1.into_group();

    let input_assignment_wth_one =
        cfg_iter!(input_assignment).map(|s| s.into_bigint()).collect::<Vec<_>>();

    let mut assignment = vec![];
    assignment.extend_from_slice(&input_assignment_wth_one[1..]);
    assignment.extend_from_slice(&aux_assignment);

    // Compute A
    let a_acc_time = start_timer!(|| "Compute A");
    let r_g1 = delta_g1_proj.mul_bigint(r_repr);
    let g_a = calculate_coeff(r_g1, &pk_common.a_query, vk.alpha_g1, &assignment);
    end_timer!(a_acc_time);

    // Compute B in G1 if needed
    let g1_b = if !r.is_zero() {
        let b_g1_acc_time = start_timer!(|| "Compute B in G1");
        let s_g1 = delta_g1_proj.mul_bigint(s_repr);
        let g1_b = calculate_coeff(s_g1, &pk_common.b_g1_query, pk_common.beta_g1, &assignment);
        end_timer!(b_g1_acc_time);

        g1_b
    } else {
        E::G1::zero()
    };

    // Compute B in G2
    let b_g2_acc_time = start_timer!(|| "Compute B in G2");
    let s_g2 = vk.delta_g2.into_group().mul_bigint(s_repr);
    let g2_b = calculate_coeff(s_g2, &pk_common.b_g2_query, vk.beta_g2, &assignment);
    drop(assignment);

    end_timer!(b_g2_acc_time);

    let c_time = start_timer!(|| "Finish C");
    let mut g_c = g_a.mul_bigint(s_repr);
    g_c += &g1_b.mul_bigint(r_repr);
    g_c -= &delta_g1_proj.mul_bigint(rs_repr);
    g_c += &l_aux_acc;
    g_c += &h_acc;
    g_c -= &v_eta_delta_inv;
    end_timer!(c_time);

    // Compute D
    let d_acc_time = start_timer!(|| "Compute D");

    let gamma_abc_inputs_source = &vk.gamma_abc_g1[input_assignment_wth_one.len()
        ..input_assignment_wth_one.len() + committed_witnesses.len()];
    let gamma_abc_inputs_acc = E::G1::msm_bigint(gamma_abc_inputs_source, &committed_witnesses);

    let v_eta_gamma_inv = vk.eta_gamma_inv_g1.into_group().mul_bigint(v_repr);

    let mut g_d = gamma_abc_inputs_acc;
    g_d += &v_eta_gamma_inv;
    end_timer!(d_acc_time);

    let committed_witnesses = witness_assignment[..vk.commit_witness_count].to_vec();
    drop(aux_assignment);

    Ok((
        Proof {
            a: g_a.into_affine(),
            b: g2_b.into_affine(),
            c: g_c.into_affine(),
            d: g_d.into_affine(),
        },
        committed_witnesses,
    ))
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
    let h =
        QAP::witness_map::<E::ScalarField, GeneralEvaluationDomain<E::ScalarField>>(cs.clone())?;
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
