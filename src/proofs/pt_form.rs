use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::EqGadget, ToBitsGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};

use crate::{
    constants::W,
    primitives::{
        poseidon::HPrime,
        secp256k1::{
            constraints::{Secp256k1Gadget, SecretKeyVar},
            SecretKey, ONE_KEY,
        },
    },
    protocols::{Params, TokenGadget},
};

#[derive(Clone)]
pub struct Witness<F: PrimeField> {
    pub pt: F,
    pub v: F,
    pub ask: SecretKey,
    pub rho_sn: F,
    pub rho_pt: F,
    pub aux_pt: Vec<Vec<bool>>,
}

impl<F: PrimeField> Default for Witness<F> {
    fn default() -> Self {
        Self {
            pt: Default::default(),
            v: Default::default(),
            ask: ONE_KEY,
            rho_sn: Default::default(),
            rho_pt: Default::default(),
            aux_pt: HPrime::EXTENSIONS.iter().map(|(n, _, _)| vec![false; *n]).collect(),
        }
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
        let Witness { pt, v, ask, rho_sn, rho_pt, aux_pt } = w;

        let v = FpVar::new_witness(cs.clone(), || Ok(v))?;
        let pt = FpVar::new_witness(cs.clone(), || Ok(pt))?;
        let ask = ask.secret_bytes().to_vec();
        let sk0 =
            FpVar::new_witness(cs.clone(), || Ok(E::ScalarField::from_be_bytes_mod_order(&ask[16..])))?;
        let sk1 =
            FpVar::new_witness(cs.clone(), || Ok(E::ScalarField::from_be_bytes_mod_order(&ask[..16])))?;
        let rho_sn = FpVar::new_witness(cs.clone(), || Ok(rho_sn))?;
        let ask = SecretKeyVar([&sk0.to_bits_le()?[..128], &sk1.to_bits_le()?[..128]].concat());
        let rho_pt = FpVar::new_witness(cs.clone(), || Ok(rho_pt))?;
        let aux_pt = aux_pt
            .iter()
            .map(|x| Vec::new_witness(cs.clone(), || Ok(x.clone())))
            .collect::<Result<Vec<_>, _>>()?;

        let apk = Secp256k1Gadget::pk_gen::<_, W>(&ask)?;

        pt.enforce_equal(&TokenGadget::pt_gen(pp, &apk, v, rho_sn, rho_pt, &aux_pt)?)?;

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
        protocols::TK,
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let (ask, apk) = secp256k1::Secp256k1::new().generate_keypair(rng);

        let v = Fr::rand(rng);
        let rho_sn = Fr::rand(rng);
        let rho_pt = Fr::rand(rng);

        let (pt, aux_pt) = TK::pt_gen(pp, &apk, v, rho_sn, rho_pt);

        let r_v = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);
        let r_rho_sn = Fr::rand(rng);

        let w = Witness { pt, v, ask, rho_sn, rho_pt, aux_pt };
        let link_v = vec![r_v, r_pt, r_sk0, r_sk1, r_rho_sn];

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

        let r_v = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);
        let r_rho_sn = Fr::rand(rng);

        let link_v = vec![r_v, r_pt, r_sk0, r_sk1, r_rho_sn];

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

        let (ask, apk) = secp256k1::Secp256k1::new().generate_keypair(rng);

        let v = Fr::rand(rng);
        let rho_sn = Fr::rand(rng);
        let rho_pt = Fr::rand(rng);

        let (pt, aux_pt) = TK::pt_gen(pp, &apk, v, rho_sn, rho_pt);

        let r_v = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);
        let r_rho_sn = Fr::rand(rng);

        let w = Witness { pt, v, ask, rho_sn, rho_pt, aux_pt };
        let link_v = vec![r_v, r_pt, r_sk0, r_sk1, r_rho_sn];

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

        let (ask, apk) = secp256k1::Secp256k1::new().generate_keypair(rng);

        let v = Fr::rand(rng);
        let rho_sn = Fr::rand(rng);
        let rho_pt = Fr::rand(rng);

        let (pt, aux_pt) = TK::pt_gen(pp, &apk, v, rho_sn, rho_pt);

        let r_v = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_sk0 = Fr::rand(rng);
        let r_sk1 = Fr::rand(rng);
        let r_rho_sn = Fr::rand(rng);

        let w = Witness { pt, v, ask, rho_sn, rho_pt, aux_pt };
        let link_v = vec![r_v, r_pt, r_sk0, r_sk1, r_rho_sn];

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

        b.iter(|| {
            verify_proof_incl_cp_link(&pvk_link, &params_link.vk, &proof_link, &[]).unwrap()
        })
    }
}
