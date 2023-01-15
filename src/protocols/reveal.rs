use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use ark_relations::r1cs::SynthesisError;
use num::{bigint::RandBigInt, BigUint};
use rand::Rng;

use super::{Params, SNRange, SecretToken, CRS, SN};
use crate::{
    lego::{
        create_random_proof_incl_cp_link, prepare_verifying_key, verify_proof_incl_cp_link,
        ProofWithLink,
    },
    primitives::{
        accumulator::IntegerCommitment,
        secp256k1::{PublicKey, SecretKey},
    },
    proofs::{bind_id, pt_form, range, sn_form, sn_range, membership::{mem, mem_and_nonmem}},
};

pub struct Statement<E: Pairing> {
    pub pt_minted: mem::Statement<E>,
    pub sn_not_spent: mem_and_nonmem::Statement<E>,
    pub range: range::Statement<E::ScalarField>,
    pub bind_id: bind_id::Statement,
}

pub struct Proof<E: Pairing> {
    pub pt_minted: mem::Proof<E>,
    pub sn_not_spent: mem_and_nonmem::Proof<E>,
    pub pt_form: ProofWithLink<E>,
    pub sn_form: ProofWithLink<E>,
    pub sn_range: ProofWithLink<E>,
    pub range: ProofWithLink<E>,
    pub bind_id: ProofWithLink<E>,
}

pub struct Reveal {}

impl Reveal {
    pub fn prove<R: Rng, E: Pairing>(
        pp: &Params<E>,
        crs: &CRS<E>,
        rng: &mut R,
        a_pt: BigUint,
        w_pt: BigUint,
        a_h_range: BigUint,
        w_h_range: BigUint,
        a_revoked_h_range: BigUint,
        w_revoked_h_range: BigUint,
        ask: SecretKey,
        st: SecretToken<E::ScalarField>,
        pt: E::ScalarField,
        sn_range: (E::ScalarField, E::ScalarField),
        bounds: (E::ScalarField, E::ScalarField),
        wpk: PublicKey,
        omega: SecretKey,
    ) -> Result<(Statement<E>, Proof<E>), SynthesisError> {
        let SecretToken { v, rho_sn, rho_pt, aux_pt } = st;

        let sn = SN::sn_gen(pp, &ask, rho_sn);
        let (h_range, aux_h_range) = SNRange::h_range_gen(pp, sn_range);
        let pt_bn: BigUint = pt.into();
        let h_range_bn: BigUint = h_range.into();

        let r_v = E::ScalarField::rand(rng);
        let r_pt = E::ScalarField::rand(rng);
        let r_sn = E::ScalarField::rand(rng);
        let r_sk0 = E::ScalarField::rand(rng);
        let r_sk1 = E::ScalarField::rand(rng);
        let r_rho_sn = E::ScalarField::rand(rng);
        let r_h_range = E::ScalarField::rand(rng);

        let pi_pt_form = create_random_proof_incl_cp_link(
            pt_form::Circuit { pp, w: pt_form::Witness { pt, v, ask, rho_sn, rho_pt, aux_pt } },
            E::ScalarField::rand(rng),
            &[r_v, r_pt, r_sk0, r_sk1, r_rho_sn],
            &crs.pt_form,
            rng,
        )?;

        let pi_sn_form = create_random_proof_incl_cp_link(
            sn_form::Circuit { pp, w: sn_form::Witness { sn, ask, rho_sn } },
            E::ScalarField::rand(rng),
            &[r_sn, r_sk0, r_sk1, r_rho_sn],
            &crs.sn_form,
            rng,
        )?;

        let pi_sn_range = create_random_proof_incl_cp_link(
            sn_range::Circuit {
                pp,
                w: sn_range::Witness { sn, h_range, range: sn_range, aux_h_range },
            },
            v,
            &[r_sn, r_h_range],
            &crs.sn_range,
            rng,
        )?;

        let s_range = range::Statement { l: bounds.0, u: bounds.1 };
        let pi_range = create_random_proof_incl_cp_link(
            range::Circuit { pp, s: s_range.clone(), w: range::Witness { v } },
            E::ScalarField::rand(rng),
            &[r_v],
            &crs.range,
            rng,
        )?;

        let s_bind_id = bind_id::Statement { wpk };
        let pi_bind_id = create_random_proof_incl_cp_link(
            bind_id::Circuit { pp, s: s_bind_id.clone(), w: bind_id::Witness { ask, omega } },
            E::ScalarField::rand(rng),
            &[r_sk0, r_sk1],
            &crs.bind_id,
            rng,
        )?;

        let rr_pt = rng.gen_biguint_below(&pp.r.n);
        let cc_pt = IntegerCommitment::commit(&pp.r, &pt_bn, &rr_pt);

        let s_mem_pt = mem::Statement { c_e_n: cc_pt, c_e_q: pi_pt_form.link_d[1], a: a_pt };
        let pi_mem_pt = mem::prove(
            pp,
            &s_mem_pt,
            &mem::Witness { w: w_pt, e: pt_bn.into(), r_n: rr_pt.into(), r_q: r_pt },
        );

        let rr_h_range = rng.gen_biguint_below(&pp.r.n);
        let cc_h_range = IntegerCommitment::commit(&pp.r, &h_range_bn, &rr_h_range);

        let s_mem_and_nonmem_h_range = mem_and_nonmem::Statement { c_e_n: cc_h_range, c_e_q: pi_sn_range.link_d[1], a_mem: a_h_range, a_nonmem: a_revoked_h_range };
        let pi_mem_and_nonmem_h_range = mem_and_nonmem::prove(
            pp,
            &s_mem_and_nonmem_h_range,
            &mem_and_nonmem::Witness {
                w_mem: w_h_range,
                w_nonmem: w_revoked_h_range,
                e: h_range_bn.into(),
                r_n: rr_h_range.into(),
                r_q: r_h_range,
            },
        );

        Ok((
            Statement {
                pt_minted: s_mem_pt,
                sn_not_spent: s_mem_and_nonmem_h_range,
                range: s_range,
                bind_id: s_bind_id,
            },
            Proof {
                pt_minted: pi_mem_pt,
                sn_not_spent: pi_mem_and_nonmem_h_range,
                pt_form: pi_pt_form,
                sn_form: pi_sn_form,
                sn_range: pi_sn_range,
                range: pi_range,
                bind_id: pi_bind_id,
            },
        ))
    }

    pub fn verify<E: Pairing>(
        pp: &Params<E>,
        crs: &CRS<E>,
        s: &Statement<E>,
        pi: &Proof<E>,
    ) -> Result<bool, SynthesisError> {
        Ok(mem::verify(pp, &s.pt_minted, &pi.pt_minted)
            && mem_and_nonmem::verify(pp, &s.sn_not_spent, &pi.sn_not_spent)
            && verify_proof_incl_cp_link(
                &prepare_verifying_key(&crs.pt_form.vk.groth16_vk),
                &crs.pt_form.vk,
                &pi.pt_form,
                &[],
            )?
            && verify_proof_incl_cp_link(
                &prepare_verifying_key(&crs.sn_form.vk.groth16_vk),
                &crs.sn_form.vk,
                &pi.sn_form,
                &[],
            )?
            && verify_proof_incl_cp_link(
                &prepare_verifying_key(&crs.sn_range.vk.groth16_vk),
                &crs.sn_range.vk,
                &pi.sn_range,
                &[],
            )?
            && verify_proof_incl_cp_link(
                &prepare_verifying_key(&crs.range.vk.groth16_vk),
                &crs.range.vk,
                &pi.range,
                &s.range.inputize(),
            )?
            && verify_proof_incl_cp_link(
                &prepare_verifying_key(&crs.bind_id.vk.groth16_vk),
                &crs.bind_id.vk,
                &pi.bind_id,
                &s.bind_id.inputize(),
            )?
            && s.pt_minted.c_e_q == pi.pt_form.link_d[1]
            && s.sn_not_spent.c_e_q == pi.sn_range.link_d[1]
            && pi.pt_form.link_d[2] == pi.sn_form.link_d[1]
            && pi.pt_form.link_d[3] == pi.sn_form.link_d[2]
            && pi.pt_form.link_d[4] == pi.sn_form.link_d[3]
            && pi.pt_form.link_d[0] == pi.range.link_d[0]
            && pi.pt_form.link_d[2] == pi.bind_id.link_d[0]
            && pi.pt_form.link_d[3] == pi.bind_id.link_d[1]
            && pi.sn_form.link_d[0] == pi.sn_range.link_d[0])
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use ark_bn254::{Bn254, Fr};
    use ark_ff::PrimeField;
    use rand::thread_rng;
    use secp256k1::SECP256K1;

    use super::*;
    use crate::{primitives::accumulator::Accumulator, protocols::mint::mint};

    #[test]
    fn test() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();
        let pp = &Params::default();

        let crs = CRS::<Bn254>::setup(pp, rng)?;

        let (v_lb, v_ub) = {
            let l = Fr::from(rng.gen_biguint_below(&Fr::MODULUS_MINUS_ONE_DIV_TWO.into()));
            let u = Fr::from(rng.gen_biguint_below(&Fr::MODULUS_MINUS_ONE_DIV_TWO.into()));

            (l.min(u), l.max(u))
        };

        let v = Fr::from(rng.gen_biguint_range(&v_lb.into(), &v_ub.into()));

        let w_pt = rng.gen_biguint_below(&pp.r.n);
        let w_h_range = rng.gen_biguint_below(&pp.r.n);
        let w_revoked_h_range = rng.gen_biguint_below(&pp.r.n);

        let (wsk, wpk) = SECP256K1.generate_keypair(rng);
        let omega = SecretKey::new(rng);
        let ask = wsk.add_tweak(&omega.into())?;
        let apk = ask.public_key(SECP256K1);
        let (st, pt) = mint(pp, rng, &apk, v);
        let a_pt = Accumulator::acc(&pp.r, &w_pt, &pt.into());
        let sn = SN::sn_gen(pp, &ask, st.rho_sn);

        let sn_lb = rng.gen_biguint_below(&sn.into()).into();
        let sn_ub = rng.gen_biguint_range(&sn.into(), &Fr::MODULUS_MINUS_ONE_DIV_TWO.into()).into();
        let (h_range, _) = SNRange::h_range_gen(pp, (sn_lb, sn_ub));
        let a_h_range = Accumulator::acc(&pp.r, &w_h_range, &h_range.into());
        let a_revoked_h_range = Accumulator::acc(&pp.r, &pp.r.g, &w_revoked_h_range);

        let (s, pi) = Reveal::prove(
            pp,
            &crs,
            rng,
            a_pt,
            w_pt,
            a_h_range,
            w_h_range,
            a_revoked_h_range,
            w_revoked_h_range,
            ask,
            st,
            pt,
            (sn_lb, sn_ub),
            (v_lb, v_ub),
            wpk,
            omega,
        )?;
        assert!(Reveal::verify(pp, &crs, &s, &pi)?);
        Ok(())
    }
}
