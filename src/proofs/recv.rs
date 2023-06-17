use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    fields::fp::FpVar,
    prelude::{Boolean, EqGadget},
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use serde::{Deserialize, Serialize};
use serde_with::serde_as;

use crate::{
    constants::W,
    primitives::{
        poseidon::{constraints::EncryptionGadget, HFieldGadget, HPrime},
        secp256k1::constraints::{PointVar, Secp256k1Gadget, SecretKeyVar},
    },
    protocols::{Params, TokenGadget},
};

#[serde_as]
#[derive(Clone, Serialize, Deserialize)]
pub struct Statement<F: PrimeField> {
    pub pt_r: F,
    pub extra: Vec<F>,
    #[serde_as(as = "crate::utils::SerdeAs")]
    pub epk_s: ark_secp256k1::Affine,
    pub nonce: F,
}

impl<F: PrimeField> Default for Statement<F> {
    fn default() -> Self {
        Self {
            pt_r: Default::default(),
            extra: vec![F::zero(); 4],
            epk_s: Default::default(),
            nonce: Default::default(),
        }
    }
}

impl<F: PrimeField> Statement<F> {
    pub fn inputize(&self) -> Vec<F> {
        let mut input = vec![self.pt_r];
        input.extend(self.extra.clone());
        input.extend(PointVar::<F, W>::inputize(&self.epk_s));
        input.push(self.nonce);
        input
    }
}

#[derive(Clone)]
pub struct Witness<F: PrimeField> {
    pub v: F,
    pub apk_r: ark_secp256k1::Affine,
    pub rho_pt_r: F,
    pub aux_pt_r: Vec<Vec<bool>>,
    pub esk_s: ark_secp256k1::Fr,
}

impl<F: PrimeField> Default for Witness<F> {
    fn default() -> Self {
        Self {
            v: Default::default(),
            apk_r: Default::default(),
            rho_pt_r: Default::default(),
            aux_pt_r: HPrime::EXTENSIONS.iter().map(|(n, _, _)| vec![false; *n]).collect(),
            esk_s: Default::default(),
        }
    }
}

pub struct Circuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub s: Statement<E::ScalarField>,
    pub w: Witness<E::ScalarField>,
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for Circuit<'a, E> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<E::ScalarField>,
    ) -> Result<(), SynthesisError> {
        let Self { pp, s, w } = self;
        let Statement { pt_r, extra, epk_s, nonce } = s;
        let Witness { v, apk_r, rho_pt_r, aux_pt_r, esk_s } = w;

        let v = FpVar::new_witness(cs.clone(), || Ok(v))?;
        let pt_r = FpVar::new_input(cs.clone(), || Ok(pt_r))?;
        let extra = Vec::new_input(cs.clone(), || Ok(extra))?;
        let epk_s = PointVar::<_, W>::new_input(cs.clone(), || Ok(epk_s))?;
        let nonce = FpVar::new_input(cs.clone(), || Ok(nonce))?;

        let apk_r = PointVar::<_, W>::new_witness(cs.clone(), || Ok(apk_r))?;
        let rho_pt_r = FpVar::new_witness(cs.clone(), || Ok(rho_pt_r))?;
        let aux_pt_r = aux_pt_r
            .iter()
            .map(|x| Vec::new_witness(cs.clone(), || Ok(x.clone())))
            .collect::<Result<Vec<_>, _>>()?;
        let esk_s = SecretKeyVar::new_witness(cs.clone(), || Ok(esk_s))?;

        pt_r.enforce_equal(&TokenGadget::pt_gen::<_, W>(
            pp,
            apk_r.hash_to_field_var(&pp.h)?,
            v.clone(),
            rho_pt_r.clone(),
            &aux_pt_r,
        )?)?;
        epk_s.enforce_equal(&Secp256k1Gadget::pk_gen(&esk_s)?)?;
        extra.enforce_equal(&EncryptionGadget::encrypt(
            &pp.h,
            vec![v, rho_pt_r, Boolean::le_bits_to_fp_var(&aux_pt_r.concat())?],
            Secp256k1Gadget::key_exchange(&esk_s, &apk_r)?.hash_to_field_var(&pp.h)?,
            nonce,
        )?)?;

        println!("{}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use ark_bn254::{Bn254, Fr};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInteger, UniformRand};
    use ark_serialize::CanonicalSerialize;
    use rand::thread_rng;

    use super::*;
    use crate::{
        lego::{
            create_random_proof_incl_cp_link, generate_random_parameters_incl_cp_link,
            prepare_verifying_key, verify_proof_incl_cp_link,
        },
        primitives::poseidon::{Encryption, HField},
        protocols::TK,
        utils::{OnChainVerifiable, ToTransaction},
    };

    #[test]
    fn test_decrypt() {
        let rng = &mut ark_std::test_rng();

        let pp = &Params::<Bn254>::default();

        let esk_s = ark_secp256k1::Fr::rand(rng);
        let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();

        let ask_r = ark_secp256k1::Fr::rand(rng);
        let apk_r = (ark_secp256k1::Affine::generator() * ask_r).into_affine();

        let mut m = vec![];
        for _ in 0..3 {
            m.push(Fr::rand(rng));
        }
        let dk = (apk_r * esk_s).hash_to_field(&pp.h);
        let nonce = Fr::rand(rng);

        let c = Encryption::encrypt(&pp.h, m.clone(), dk, nonce);

        let now = Instant::now();
        for _ in 0..10000 {
            let dk = (epk_s * ask_r).hash_to_field(&pp.h);
            assert_eq!(m, Encryption::decrypt(&pp.h, c.clone(), dk, nonce).unwrap());
        }
        println!("{:?}", now.elapsed());
    }

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let esk_s = ark_secp256k1::Fr::rand(rng);
        let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();

        let apk_r = ark_secp256k1::Affine::rand(rng);
        let h_apk_r = apk_r.hash_to_field(&pp.h);

        let v = Fr::rand(rng);
        let rho_pt_r = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let (pt_r, aux_pt_r) = TK::pt_gen(pp, h_apk_r, v, rho_pt_r);

        let dk = (apk_r * esk_s).hash_to_field(&pp.h);
        let extra = Encryption::encrypt(
            &pp.h,
            vec![
                v,
                rho_pt_r,
                Fr::from_bigint(<Fr as PrimeField>::BigInt::from_bits_le(&aux_pt_r.concat()))
                    .unwrap(),
            ],
            dk,
            nonce,
        );

        let r_v = Fr::rand(rng);

        let s = Statement { pt_r, extra, epk_s, nonce };
        let w = Witness { v, apk_r, rho_pt_r, aux_pt_r, esk_s };
        let public_input = s.inputize();

        let link_v = vec![r_v];

        let params_link = generate_random_parameters_incl_cp_link::<Bn254, _, _>(
            Circuit { pp, s: Default::default(), w: Default::default() },
            &pp.c,
            link_v.len(),
            rng,
        )
        .unwrap();

        println!("{}", params_link.compressed_size());

        let pvk_link = prepare_verifying_key(&params_link.vk.groth16_vk);
        let proof_link = create_random_proof_incl_cp_link(
            Circuit { pp, s, w },
            Fr::rand(rng),
            &link_v,
            &params_link,
            rng,
        )
        .unwrap();

        println!("{}", proof_link.compressed_size());

        assert!(verify_proof_incl_cp_link(&pvk_link, &params_link.vk, &proof_link, &public_input)
            .unwrap());

        println!("{}", params_link.vk.to_on_chain_verifier("Recv"));
        println!(
            "{}",
            vec![
                proof_link.groth16_proof.a.to_tx(),
                proof_link.groth16_proof.b.to_tx(),
                proof_link.groth16_proof.c.to_tx(),
                vec![proof_link.link_d, vec![proof_link.groth16_proof.d], vec![proof_link.link_pi]]
                    .concat()
                    .to_tx(),
                public_input.to_tx()
            ]
            .join(",")
        );
    }

    #[bench]
    fn bench_keygen(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let r_v = Fr::rand(rng);

        let link_v = vec![r_v];

        b.iter(|| {
            generate_random_parameters_incl_cp_link::<Bn254, _, _>(
                Circuit { pp, w: Default::default(), s: Default::default() },
                &pp.c,
                link_v.len(),
                rng,
            )
            .unwrap()
        });
    }

    #[bench]
    fn bench_prove(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let esk_s = ark_secp256k1::Fr::rand(rng);
        let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();

        let apk_r = ark_secp256k1::Affine::rand(rng);
        let h_apk_r = apk_r.hash_to_field(&pp.h);

        let v = Fr::rand(rng);
        let rho_pt_r = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let (pt_r, aux_pt_r) = TK::pt_gen(pp, h_apk_r, v, rho_pt_r);

        let dk = (apk_r * esk_s).hash_to_field(&pp.h);
        let extra = Encryption::encrypt(
            &pp.h,
            vec![
                v,
                rho_pt_r,
                Fr::from_bigint(<Fr as PrimeField>::BigInt::from_bits_le(&aux_pt_r.concat()))
                    .unwrap(),
            ],
            dk,
            nonce,
        );

        let r_v = Fr::rand(rng);

        let s = Statement { pt_r, extra, epk_s, nonce };
        let w = Witness { v, apk_r, rho_pt_r, aux_pt_r, esk_s };

        let link_v = vec![r_v];

        let params_link = generate_random_parameters_incl_cp_link::<Bn254, _, _>(
            Circuit { pp, s: Default::default(), w: Default::default() },
            &pp.c,
            link_v.len(),
            rng,
        )
        .unwrap();

        b.iter(|| {
            create_random_proof_incl_cp_link(
                Circuit { pp, s: s.clone(), w: w.clone() },
                Fr::rand(rng),
                &link_v,
                &params_link,
                rng,
            )
            .unwrap()
        });
    }

    #[bench]
    fn bench_verify(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let esk_s = ark_secp256k1::Fr::rand(rng);
        let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();

        let apk_r = ark_secp256k1::Affine::rand(rng);
        let h_apk_r = apk_r.hash_to_field(&pp.h);

        let v = Fr::rand(rng);
        let rho_pt_r = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let (pt_r, aux_pt_r) = TK::pt_gen(pp, h_apk_r, v, rho_pt_r);

        let dk = (apk_r * esk_s).hash_to_field(&pp.h);
        let extra = Encryption::encrypt(
            &pp.h,
            vec![
                v,
                rho_pt_r,
                Fr::from_bigint(<Fr as PrimeField>::BigInt::from_bits_le(&aux_pt_r.concat()))
                    .unwrap(),
            ],
            dk,
            nonce,
        );

        let r_v = Fr::rand(rng);

        let s = Statement { pt_r, extra, epk_s, nonce };
        let w = Witness { v, apk_r, rho_pt_r, aux_pt_r, esk_s };
        let public_input = s.inputize();

        let link_v = vec![r_v];

        let params_link = generate_random_parameters_incl_cp_link::<Bn254, _, _>(
            Circuit { pp, s: Default::default(), w: Default::default() },
            &pp.c,
            link_v.len(),
            rng,
        )
        .unwrap();

        let pvk_link = prepare_verifying_key(&params_link.vk.groth16_vk);
        let proof_link = create_random_proof_incl_cp_link(
            Circuit { pp, s, w },
            Fr::rand(rng),
            &link_v,
            &params_link,
            rng,
        )
        .unwrap();

        b.iter(|| {
            verify_proof_incl_cp_link(&pvk_link, &params_link.vk, &proof_link, &public_input)
                .unwrap()
        })
    }
}
