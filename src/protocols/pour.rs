use std::ops::Mul;

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField, UniformRand};
use ark_relations::r1cs::SynthesisError;
use num::{bigint::RandBigInt, BigUint};
use rand::Rng;

use super::{Params, SecretToken, CRS, SN, TK};
use crate::{
    lego::{
        create_random_proof_incl_cp_link, prepare_verifying_key, verify_proof_incl_cp_link,
        ProofWithLink,
    },
    primitives::{
        accumulator::IntegerCommitment,
        poseidon::{Encryption, HField},
    },
    proofs::{membership::mem, pt_form, recv, sn_form},
};

pub struct Statement<E: Pairing> {
    pub mem: mem::Statement<E>,
    pub recv: recv::Statement<E::ScalarField>,
    pub sn_s: E::ScalarField,
    pub r_sn_s: E::ScalarField,
}

pub struct Proof<E: Pairing> {
    pub mem: mem::Proof<E>,
    pub sn_form: ProofWithLink<E>,
    pub pt_form: ProofWithLink<E>,
    pub recv: ProofWithLink<E>,
}

pub struct Pour {}

impl Pour {
    pub fn prove<R: Rng, E: Pairing>(
        pp: &Params<E>,
        crs: &CRS<E>,
        rng: &mut R,
        a_pt: BigUint,
        w_pt: BigUint,
        ask_s: ark_secp256k1::Fr,
        st_s: SecretToken<E::ScalarField>,
        pt_s: E::ScalarField,
        apk_r: ark_secp256k1::Affine,
    ) -> Result<(SecretToken<E::ScalarField>, Statement<E>, Proof<E>), SynthesisError> {
        let pt_s_bn: BigUint = pt_s.into();
        let SecretToken { v, rho_pt: rho_pt_s, aux_pt: aux_pt_s } = st_s;
        let rho_pt_r = E::ScalarField::rand(rng);
        let nonce = E::ScalarField::rand(rng);

        let (pt_r, aux_pt_r) = TK::pt_gen(pp, apk_r.hash_to_field(&pp.h), v, rho_pt_r);
        let esk_s = ark_secp256k1::Fr::rand(rng);
        let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();

        let dk = (apk_r * esk_s).hash_to_field(&pp.h);
        let extra = Encryption::encrypt(
            &pp.h,
            vec![
                v,
                rho_pt_r,
                E::ScalarField::from_bigint(<E::ScalarField as PrimeField>::BigInt::from_bits_le(
                    &aux_pt_r.concat(),
                ))
                .unwrap(),
            ],
            dk,
            nonce,
        );
        let sn_s = SN::sn_gen(pp, &ask_s, pt_s);

        let h_apk_s = (ark_secp256k1::Affine::generator() * ask_s).hash_to_field(&pp.h);

        let r_v = E::ScalarField::rand(rng);
        let r_pt_s = E::ScalarField::rand(rng);
        let r_sn_s = E::ScalarField::rand(rng);
        let r_h_apk_s = E::ScalarField::rand(rng);

        let pi_pt_form = create_random_proof_incl_cp_link(
            pt_form::Circuit {
                pp,
                w: pt_form::Witness {
                    pt: pt_s,
                    v,
                    h_apk: h_apk_s,
                    rho_pt: rho_pt_s,
                    aux_pt: aux_pt_s,
                },
            },
            E::ScalarField::rand(rng),
            &[r_v, r_pt_s, r_h_apk_s],
            &crs.pt_form,
            rng,
        )?;

        let pi_sn_form = create_random_proof_incl_cp_link(
            sn_form::Circuit {
                pp,
                w: sn_form::Witness { sn: sn_s, ask: ask_s, pt: pt_s, h_apk: h_apk_s },
            },
            E::ScalarField::rand(rng),
            &[r_sn_s, r_pt_s, r_h_apk_s],
            &crs.sn_form,
            rng,
        )?;

        let s_recv = recv::Statement { pt_r, extra, epk_s, nonce };
        let pi_recv = create_random_proof_incl_cp_link(
            recv::Circuit {
                pp,
                s: s_recv.clone(),
                w: recv::Witness { v, apk_r, rho_pt_r, aux_pt_r: aux_pt_r.clone(), esk_s },
            },
            E::ScalarField::rand(rng),
            &[r_v],
            &crs.recv,
            rng,
        )?;

        let rr_pt_s = rng.gen_biguint_below(&pp.r.n);
        let cc_pt_s = IntegerCommitment::commit(&pp.r, &pt_s_bn, &rr_pt_s);

        let s_mem = mem::Statement { c_e_n: cc_pt_s, c_e_q: pi_pt_form.link_d[1], a: a_pt };
        let pi_mem = mem::prove(
            pp,
            &s_mem,
            &mem::Witness { w: w_pt, e: pt_s_bn.into(), r_n: rr_pt_s.into(), r_q: r_pt_s },
        );

        Ok((
            SecretToken { v, rho_pt: rho_pt_r, aux_pt: aux_pt_r },
            Statement { mem: s_mem, recv: s_recv, sn_s, r_sn_s },
            Proof { mem: pi_mem, sn_form: pi_sn_form, pt_form: pi_pt_form, recv: pi_recv },
        ))
    }

    pub fn verify<E: Pairing>(
        pp: &Params<E>,
        crs: &CRS<E>,
        s: &Statement<E>,
        pi: &Proof<E>,
    ) -> Result<bool, SynthesisError> {
        Ok(mem::verify(pp, &s.mem, &pi.mem)
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
                &prepare_verifying_key(&crs.recv.vk.groth16_vk),
                &crs.recv.vk,
                &pi.recv,
                &s.recv.inputize(),
            )?
            && s.mem.c_e_q == pi.pt_form.link_d[1]
            && pi.pt_form.link_d[0] == pi.recv.link_d[0]
            && pi.pt_form.link_d[1] == pi.sn_form.link_d[1]
            && pi.pt_form.link_d[2] == pi.sn_form.link_d[2]
            && pp.c.g.mul(s.sn_s) + pp.c.h.mul(s.r_sn_s) == pi.sn_form.link_d[0].into())
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use ark_bn254::{Bn254, Fr};
    use ark_ec::AffineRepr;
    use ark_ff::UniformRand;
    use rand::thread_rng;

    use super::*;
    use crate::{primitives::accumulator::Accumulator, protocols::mint::mint};

    #[test]
    fn test() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();
        let pp = &Params::default();

        let crs = CRS::<Bn254>::setup(pp, rng)?;

        let v = Fr::rand(rng);

        let w_pt = rng.gen_biguint_below(&pp.r.n);
        let ask_s = ark_secp256k1::Fr::rand(rng);
        let apk_s = (ark_secp256k1::Affine::generator() * ask_s).into_affine();
        let apk_r = ark_secp256k1::Affine::rand(rng);
        let (st_s, pt_s) = mint(pp, rng, &apk_s, v);
        let a_pt = Accumulator::acc(&pp.r, &w_pt, &pt_s.into());

        let (_, s, pi) = Pour::prove(pp, &crs, rng, a_pt, w_pt, ask_s, st_s, pt_s, apk_r)?;
        assert!(Pour::verify(pp, &crs, &s, &pi)?);
        Ok(())
    }
}
