use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::EqGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};

use crate::{
    primitives::secp256k1::{SecretKey, ONE_KEY},
    protocols::{Params, SNGadget},
};

#[derive(Clone)]
pub struct Witness<F: PrimeField> {
    pub sn: F,
    pub ask: SecretKey,
    pub rho_sn: F,
}

impl<F: PrimeField> Default for Witness<F> {
    fn default() -> Self {
        Self { sn: Default::default(), ask: ONE_KEY, rho_sn: Default::default() }
    }
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
        let Witness { sn, ask, rho_sn } = w;

        let sn = FpVar::new_witness(cs.clone(), || Ok(sn))?;
        let ask = ask.secret_bytes().to_vec();
        let sk0 = FpVar::new_witness(cs.clone(), || {
            Ok(E::ScalarField::from_be_bytes_mod_order(&ask[16..]))
        })?;
        let sk1 = FpVar::new_witness(cs.clone(), || {
            Ok(E::ScalarField::from_be_bytes_mod_order(&ask[..16]))
        })?;
        let rho_sn = FpVar::new_witness(cs.clone(), || Ok(rho_sn))?;

        sn.enforce_equal(&SNGadget::sn_gen(pp, (sk0, sk1), rho_sn)?)?;

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

    use super::*;
    use crate::{
        lego::{
            create_random_proof_incl_cp_link, generate_random_parameters_incl_cp_link,
            prepare_verifying_key, verify_proof_incl_cp_link,
        },
        protocols::SN,
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let (ask, _) = secp256k1::Secp256k1::new().generate_keypair(rng);

        let rho_sn = Fr::rand(rng);

        let sn = SN::sn_gen(pp, &ask, rho_sn);

        let r_sn = Fr::rand(rng);
        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);
        let r_rho_sn = Fr::rand(rng);

        let w = Witness { sn, ask, rho_sn };
        let link_v = vec![r_sn, r_sk0, r_sk1, r_rho_sn];

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

        assert!(verify_proof_incl_cp_link(&pvk_link, &params_link.vk, &proof_link, &[]).unwrap());
    }

    #[bench]
    fn bench_keygen(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let r_sn = Fr::rand(rng);
        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);
        let r_rho_sn = Fr::rand(rng);

        let link_v = vec![r_sn, r_sk0, r_sk1, r_rho_sn];

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

        let (ask, _) = secp256k1::Secp256k1::new().generate_keypair(rng);

        let rho_sn = Fr::rand(rng);

        let sn = SN::sn_gen(pp, &ask, rho_sn);

        let r_sn = Fr::rand(rng);
        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);
        let r_rho_sn = Fr::rand(rng);

        let w = Witness { sn, ask, rho_sn };
        let link_v = vec![r_sn, r_sk0, r_sk1, r_rho_sn];

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

        let (ask, _) = secp256k1::Secp256k1::new().generate_keypair(rng);

        let rho_sn = Fr::rand(rng);

        let sn = SN::sn_gen(pp, &ask, rho_sn);

        let r_sn = Fr::rand(rng);
        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);
        let r_rho_sn = Fr::rand(rng);

        let w = Witness { sn, ask, rho_sn };
        let link_v = vec![r_sn, r_sk0, r_sk1, r_rho_sn];

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
