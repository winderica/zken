use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use serde::{Deserialize, Serialize};
use serde_with::serde_as;

use crate::{
    constants::W,
    primitives::{
        poseidon::HFieldGadget,
        secp256k1::constraints::{PointVar, Secp256k1Gadget, SecretKeyVar},
    },
    protocols::Params,
};

#[serde_as]
#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Statement {
    #[serde_as(as = "crate::utils::SerdeAs")]
    pub wpk: ark_secp256k1::Affine,
}

impl Statement {
    pub fn inputize<F: PrimeField>(&self) -> Vec<F> {
        PointVar::<F, W>::inputize(&self.wpk)
    }
}

#[derive(Clone, Default)]
pub struct Witness<F: PrimeField> {
    pub h_apk: F,
    pub delta: ark_secp256k1::Fr,
}

pub struct Circuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub s: Statement,
    pub w: Witness<E::ScalarField>,
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for Circuit<'a, E> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<E::ScalarField>,
    ) -> ark_relations::r1cs::Result<()> {
        let Self { s, w, pp } = self;
        let Statement { wpk } = s;
        let Witness { h_apk, delta } = w;

        let h_apk = FpVar::<E::ScalarField>::new_witness(cs.clone(), || Ok(h_apk))?;
        let delta = SecretKeyVar::new_witness(cs.clone(), || Ok(delta))?;

        let wpk = PointVar::<E::ScalarField, W>::new_input(cs.clone(), || Ok(wpk))?;

        wpk.add(&Secp256k1Gadget::pk_gen(&delta)?)?
            .hash_to_field_var(&pp.h)?
            .enforce_equal(&h_apk)?;

        println!("{}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalSerialize;
    use rand::thread_rng;

    use super::*;
    use crate::{
        lego::{
            create_random_proof_incl_cp_link, generate_random_parameters_incl_cp_link,
            prepare_verifying_key, verify_proof_incl_cp_link,
        },
        primitives::poseidon::HField,
        utils::{OnChainVerifiable, ToTransaction},
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let wsk = ark_secp256k1::Fr::rand(rng);
        let wpk = (ark_secp256k1::Affine::generator() * wsk).into_affine();
        let delta = ark_secp256k1::Fr::rand(rng);
        let ask = wsk + delta;
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_h_apk = Fr::rand(rng);

        let s = Statement { wpk };
        let w = Witness { h_apk, delta };
        let public_input = s.inputize();

        let link_v = vec![r_h_apk];

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

        println!("{}", params_link.vk.to_on_chain_verifier("BindID"));
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

        let r_h_apk = Fr::rand(rng);

        let link_v = vec![r_h_apk];

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

        let wsk = ark_secp256k1::Fr::rand(rng);
        let wpk = (ark_secp256k1::Affine::generator() * wsk).into_affine();
        let delta = ark_secp256k1::Fr::rand(rng);
        let ask = wsk + delta;
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_h_apk = Fr::rand(rng);

        let s = Statement { wpk };
        let w = Witness { h_apk, delta };

        let link_v = vec![r_h_apk];

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

        let wsk = ark_secp256k1::Fr::rand(rng);
        let wpk = (ark_secp256k1::Affine::generator() * wsk).into_affine();
        let delta = ark_secp256k1::Fr::rand(rng);
        let ask = wsk + delta;
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_h_apk = Fr::rand(rng);

        let s = Statement { wpk };
        let w = Witness { h_apk, delta };
        let public_input = s.inputize();

        let link_v = vec![r_h_apk];

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
