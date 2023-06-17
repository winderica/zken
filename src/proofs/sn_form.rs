use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::EqGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};

use crate::{
    constants::W,
    primitives::{
        poseidon::HFieldGadget,
        secp256k1::constraints::{Secp256k1Gadget, SecretKeyVar},
    },
    protocols::{Params, SNGadget},
};

#[derive(Clone, Default)]
pub struct Witness<F: PrimeField> {
    pub h_apk: F,
    pub sn: F,
    pub pt: F,
    pub ask: ark_secp256k1::Fr,
}

pub struct Circuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub w: Witness<E::ScalarField>,
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for Circuit<'a, E> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<E::ScalarField>,
    ) -> ark_relations::r1cs::Result<()> {
        let Self { pp, w } = self;
        let Witness { h_apk, sn, ask, pt } = w;

        let sn = FpVar::new_witness(cs.clone(), || Ok(sn))?;
        let pt = FpVar::new_witness(cs.clone(), || Ok(pt))?;
        let h_apk = FpVar::new_witness(cs.clone(), || Ok(h_apk))?;
        let ask = SecretKeyVar::new_witness(cs.clone(), || Ok(ask))?;

        Secp256k1Gadget::pk_gen::<_, W>(&ask)?.hash_to_field_var(&pp.h)?.enforce_equal(&h_apk)?;
        sn.enforce_equal(&SNGadget::sn_gen(pp, ask, pt)?)?;

        println!("{}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ec::AffineRepr;
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
        protocols::SN,
        utils::{OnChainVerifiable, ToTransaction},
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let ask = ark_secp256k1::Fr::rand(rng);

        let pt = Fr::rand(rng);
        let sn = SN::sn_gen(pp, &ask, pt);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_sn = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let w = Witness { sn, ask, pt, h_apk };
        let link_v = vec![r_sn, r_pt, r_h_apk];

        let params_link = generate_random_parameters_incl_cp_link::<Bn254, _, _>(
            Circuit { pp, w: Default::default() },
            &pp.c,
            link_v.len(),
            rng,
        )
        .unwrap();

        println!("{}", params_link.compressed_size());

        let pvk_link = prepare_verifying_key(&params_link.vk.groth16_vk);
        let proof_link = create_random_proof_incl_cp_link(
            Circuit { pp, w },
            Fr::rand(rng),
            &link_v,
            &params_link,
            rng,
        )
        .unwrap();

        println!("{}", proof_link.compressed_size());

        assert!(verify_proof_incl_cp_link(&pvk_link, &params_link.vk, &proof_link, &[]).unwrap());
    
        println!("{}", params_link.vk.to_on_chain_verifier("SNForm"));
        println!(
            "{}",
            vec![
                proof_link.groth16_proof.a.to_tx(),
                proof_link.groth16_proof.b.to_tx(),
                proof_link.groth16_proof.c.to_tx(),
                vec![proof_link.link_d, vec![proof_link.groth16_proof.d], vec![proof_link.link_pi]]
                    .concat()
                    .to_tx(),
                "[]".to_string()
            ]
            .join(",")
        );
    }

    #[bench]
    fn bench_keygen(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let r_sn = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let link_v = vec![r_sn, r_pt, r_h_apk];

        b.iter(|| {
            generate_random_parameters_incl_cp_link::<Bn254, _, _>(
                Circuit { pp, w: Default::default() },
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

        let ask = ark_secp256k1::Fr::rand(rng);

        let pt = Fr::rand(rng);
        let sn = SN::sn_gen(pp, &ask, pt);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_sn = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let w = Witness { sn, ask, pt, h_apk };
        let link_v = vec![r_sn, r_pt, r_h_apk];

        let params_link = generate_random_parameters_incl_cp_link::<Bn254, _, _>(
            Circuit { pp, w: Default::default() },
            &pp.c,
            link_v.len(),
            rng,
        )
        .unwrap();

        b.iter(|| {
            create_random_proof_incl_cp_link(
                Circuit { pp, w: w.clone() },
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

        let ask = ark_secp256k1::Fr::rand(rng);

        let pt = Fr::rand(rng);
        let sn = SN::sn_gen(pp, &ask, pt);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_sn = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let w = Witness { sn, ask, pt, h_apk };
        let link_v = vec![r_sn, r_pt, r_h_apk];

        let params_link = generate_random_parameters_incl_cp_link::<Bn254, _, _>(
            Circuit { pp, w: Default::default() },
            &pp.c,
            link_v.len(),
            rng,
        )
        .unwrap();

        let pvk_link = prepare_verifying_key(&params_link.vk.groth16_vk);
        let proof_link = create_random_proof_incl_cp_link(
            Circuit { pp, w },
            Fr::rand(rng),
            &link_v,
            &params_link,
            rng,
        )
        .unwrap();

        b.iter(|| verify_proof_incl_cp_link(&pvk_link, &params_link.vk, &proof_link, &[]).unwrap())
    }
}
