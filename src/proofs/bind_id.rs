use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar, ToBitsGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use serde::{Deserialize, Serialize};

use crate::{
    constants::W,
    primitives::secp256k1::{
        constraints::{PointVar, Secp256k1Gadget, SecretKeyVar},
        PublicKey, SecretKey, ONE_KEY, SECP256K1,
    },
    protocols::Params,
};

#[derive(Clone, Serialize, Deserialize)]
pub struct Statement {
    pub wpk: PublicKey,
}

impl Default for Statement {
    fn default() -> Self {
        Self { wpk: PublicKey::from_secret_key(SECP256K1, &ONE_KEY) }
    }
}

impl Statement {
    pub fn inputize<F: PrimeField>(&self) -> Vec<F> {
        PointVar::<F, W>::inputize(&self.wpk.serialize_uncompressed())
    }
}

#[derive(Clone)]
pub struct Witness {
    pub ask: SecretKey,
    pub omega: SecretKey,
}

impl Default for Witness {
    fn default() -> Self {
        Self { ask: ONE_KEY, omega: ONE_KEY }
    }
}

pub struct Circuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub s: Statement,
    pub w: Witness,
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for Circuit<'a, E> {
    fn generate_constraints(self, cs: ConstraintSystemRef<E::ScalarField>) -> ark_relations::r1cs::Result<()> {
        let Self { s, w, .. } = self;
        let Statement { wpk } = s;
        let Witness { ask, omega } = w;

        let (sk0, sk1) = {
            let ask = ask.secret_bytes().to_vec();
            let sk1 = E::ScalarField::from_be_bytes_mod_order(&ask[16..]);
            let sk0 = E::ScalarField::from_be_bytes_mod_order(&ask[..16]);
            let sk1 = FpVar::new_witness(cs.clone(), || Ok(sk1))?;
            let sk0 = FpVar::new_witness(cs.clone(), || Ok(sk0))?;
            (sk0, sk1)
        };
        let omega = SecretKeyVar::new_witness(cs.clone(), || Ok(omega.secret_bytes().to_vec()))?;

        let wpk = PointVar::<E::ScalarField, W>::new_input(cs.clone(), || {
            Ok(wpk.serialize_uncompressed().to_vec())
        })?;

        wpk.add(&Secp256k1Gadget::pk_gen(&omega)?)?
            .enforce_equal(&Secp256k1Gadget::pk_gen(&SecretKeyVar([&sk1.to_bits_le()?[..128], &sk0.to_bits_le()?[..128]].concat()))?)?;

        println!("{}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalSerialize;
    use rand::thread_rng;
    use secp256k1::SECP256K1;

    use super::*;
    use crate::lego::{
        create_random_proof_incl_cp_link, generate_random_parameters_incl_cp_link,
        prepare_verifying_key, verify_proof_incl_cp_link,
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let (wsk, wpk) = SECP256K1.generate_keypair(rng);
        let omega = SecretKey::new(rng);
        let ask = wsk.add_tweak(&omega.into()).unwrap();

        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);

        let s = Statement { wpk };
        let w = Witness { ask, omega };
        let public_input = s.inputize();

        let link_v = vec![r_sk0, r_sk1];

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

        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);

        let link_v = vec![r_sk0, r_sk1];

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

        let (wsk, wpk) = SECP256K1.generate_keypair(rng);
        let omega = SecretKey::new(rng);
        let ask = wsk.add_tweak(&omega.into()).unwrap();

        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);

        let s = Statement { wpk };
        let w = Witness { ask, omega };

        let link_v = vec![r_sk0, r_sk1];

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

        let (wsk, wpk) = SECP256K1.generate_keypair(rng);
        let omega = SecretKey::new(rng);
        let ask = wsk.add_tweak(&omega.into()).unwrap();

        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);

        let s = Statement { wpk };
        let w = Witness { ask, omega };
        let public_input = s.inputize();

        let link_v = vec![r_sk0, r_sk1];

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
