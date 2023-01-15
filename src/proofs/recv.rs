use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    fields::fp::FpVar,
    prelude::{Boolean, EqGadget},
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use serde::{Deserialize, Serialize};

use crate::{
    constants::W,
    primitives::{
        poseidon::{constraints::EncryptionGadget, HPrime},
        secp256k1::{
            constraints::{PointVar, Secp256k1Gadget, SecretKeyVar},
            PublicKey, SecretKey, ONE_KEY, SECP256K1,
        },
    },
    protocols::{Params, TokenGadget},
};

#[derive(Clone, Serialize, Deserialize)]
pub struct Statement<F: PrimeField> {
    pub pt_r: F,
    pub extra: Vec<F>,
    pub epk_s: PublicKey,
    pub nonce: F,
}

impl<F: PrimeField> Default for Statement<F> {
    fn default() -> Self {
        Self {
            pt_r: Default::default(),
            extra: vec![F::zero(); 5],
            epk_s: PublicKey::from_secret_key(SECP256K1, &ONE_KEY),
            nonce: F::zero(),
        }
    }
}

impl<F: PrimeField> Statement<F> {
    pub fn inputize(&self) -> Vec<F> {
        let mut input = vec![self.pt_r];
        input.extend(self.extra.clone());
        input.extend(PointVar::<F, W>::inputize(&self.epk_s.serialize_uncompressed()));
        input.push(self.nonce);
        input
    }
}

#[derive(Clone)]
pub struct Witness<F: PrimeField> {
    pub v: F,
    pub apk_r: PublicKey,
    pub rho_sn_r: F,
    pub rho_pt_r: F,
    pub aux_pt_r: Vec<Vec<bool>>,
    pub esk_s: SecretKey,
}

impl<F: PrimeField> Default for Witness<F> {
    fn default() -> Self {
        Self {
            v: Default::default(),
            apk_r: PublicKey::from_secret_key(SECP256K1, &ONE_KEY),
            rho_sn_r: Default::default(),
            rho_pt_r: Default::default(),
            aux_pt_r: HPrime::EXTENSIONS.iter().map(|(n, _, _)| vec![false; *n]).collect(),
            esk_s: ONE_KEY,
        }
    }
}

pub struct Circuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub s: Statement<E::ScalarField>,
    pub w: Witness<E::ScalarField>,
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for Circuit<'a, E> {
    fn generate_constraints(self, cs: ConstraintSystemRef<E::ScalarField>) -> Result<(), SynthesisError> {
        let Self { pp, s, w } = self;
        let Statement { pt_r, extra, epk_s, nonce } = s;
        let Witness { v, apk_r, rho_sn_r, rho_pt_r, aux_pt_r, esk_s } = w;

        let v = FpVar::new_witness(cs.clone(), || Ok(v))?;
        let pt_r = FpVar::new_input(cs.clone(), || Ok(pt_r))?;
        let extra = Vec::new_input(cs.clone(), || Ok(extra))?;
        let epk_s = PointVar::<_, W>::new_input(cs.clone(), || {
            Ok(epk_s.serialize_uncompressed().to_vec())
        })?;
        let nonce = FpVar::new_input(cs.clone(), || Ok(nonce))?;

        let apk_r = PointVar::<_, W>::new_witness(cs.clone(), || {
            Ok(apk_r.serialize_uncompressed().to_vec())
        })?;
        let rho_sn_r = FpVar::new_witness(cs.clone(), || Ok(rho_sn_r))?;
        let rho_pt_r = FpVar::new_witness(cs.clone(), || Ok(rho_pt_r))?;
        let aux_pt_r = aux_pt_r
            .iter()
            .map(|x| Vec::new_witness(cs.clone(), || Ok(x.clone())))
            .collect::<Result<Vec<_>, _>>()?;
        let esk_s = SecretKeyVar::new_witness(cs.clone(), || Ok(esk_s.secret_bytes().to_vec()))?;

        pt_r.enforce_equal(&TokenGadget::pt_gen(
            pp,
            &apk_r,
            v.clone(),
            rho_sn_r.clone(),
            rho_pt_r.clone(),
            &aux_pt_r,
        )?)?;
        epk_s.enforce_equal(&Secp256k1Gadget::pk_gen(&esk_s)?)?;

        let dk = Secp256k1Gadget::key_exchange(&esk_s, &apk_r)?.hash(&pp.h)?;
        extra.enforce_equal(&EncryptionGadget::encrypt(
            &pp.h,
            vec![v, rho_sn_r, rho_pt_r, Boolean::le_bits_to_fp_var(&aux_pt_r.concat())?],
            dk,
            nonce,
        )?)?;

        println!("{}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ff::{BigInteger, UniformRand};
    use ark_serialize::CanonicalSerialize;
    use rand::thread_rng;
    use secp256k1::SECP256K1;

    use super::*;
    use crate::{
        lego::{
            create_random_proof_incl_cp_link, generate_random_parameters_incl_cp_link,
            prepare_verifying_key, verify_proof_incl_cp_link,
        },
        primitives::poseidon::{Encryption, CRH},
        protocols::TK,
        utils::ToVecF,
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let (esk_s, epk_s) = SECP256K1.generate_keypair(rng);
        let (_, apk_r) = SECP256K1.generate_keypair(rng);

        let v = Fr::rand(rng);
        let rho_sn_r = Fr::rand(rng);
        let rho_pt_r = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let (pt_r, aux_pt_r) = TK::pt_gen(pp, &apk_r, v, rho_sn_r, rho_pt_r);

        let dk = apk_r.mul_tweak(SECP256K1, &esk_s.into()).unwrap();
        let dk = CRH::hash_vec(&pp.h, &dk.to_vec_f(128));
        let extra = Encryption::encrypt(
            &pp.h,
            vec![
                v,
                rho_sn_r,
                rho_pt_r,
                Fr::from_bigint(<Fr as PrimeField>::BigInt::from_bits_le(&aux_pt_r.concat()))
                    .unwrap(),
            ],
            dk,
            nonce,
        );

        let r_v = Fr::rand(rng);

        let s = Statement { pt_r, extra, epk_s, nonce };
        let w = Witness { v, apk_r, rho_sn_r, rho_pt_r, aux_pt_r, esk_s };
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

        assert!(verify_proof_incl_cp_link(&pvk_link, &params_link.vk, &proof_link, &public_input)
            .unwrap());
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

        let (esk_s, epk_s) = SECP256K1.generate_keypair(rng);
        let (_, apk_r) = SECP256K1.generate_keypair(rng);

        let v = Fr::rand(rng);
        let rho_sn_r = Fr::rand(rng);
        let rho_pt_r = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let (pt_r, aux_pt_r) = TK::pt_gen(pp, &apk_r, v, rho_sn_r, rho_pt_r);

        let dk = apk_r.mul_tweak(SECP256K1, &esk_s.into()).unwrap();
        let dk = CRH::hash_vec(&pp.h, &dk.to_vec_f(128));
        let extra = Encryption::encrypt(
            &pp.h,
            vec![
                v,
                rho_sn_r,
                rho_pt_r,
                Fr::from_bigint(<Fr as PrimeField>::BigInt::from_bits_le(&aux_pt_r.concat()))
                    .unwrap(),
            ],
            dk,
            nonce,
        );

        let r_v = Fr::rand(rng);

        let s = Statement { pt_r, extra, epk_s, nonce };
        let w = Witness { v, apk_r, rho_sn_r, rho_pt_r, aux_pt_r, esk_s };

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

        let (esk_s, epk_s) = SECP256K1.generate_keypair(rng);
        let (_, apk_r) = SECP256K1.generate_keypair(rng);

        let v = Fr::rand(rng);
        let rho_sn_r = Fr::rand(rng);
        let rho_pt_r = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let (pt_r, aux_pt_r) = TK::pt_gen(pp, &apk_r, v, rho_sn_r, rho_pt_r);

        let dk = apk_r.mul_tweak(SECP256K1, &esk_s.into()).unwrap();
        let dk = CRH::hash_vec(&pp.h, &dk.to_vec_f(128));
        let extra = Encryption::encrypt(
            &pp.h,
            vec![
                v,
                rho_sn_r,
                rho_pt_r,
                Fr::from_bigint(<Fr as PrimeField>::BigInt::from_bits_le(&aux_pt_r.concat()))
                    .unwrap(),
            ],
            dk,
            nonce,
        );

        let r_v = Fr::rand(rng);

        let s = Statement { pt_r, extra, epk_s, nonce };
        let w = Witness { v, apk_r, rho_sn_r, rho_pt_r, aux_pt_r, esk_s };
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
