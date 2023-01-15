use std::cmp::Ordering;

use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::EqGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};

use crate::{
    constants::W,
    primitives::poseidon::HPrime,
    protocols::{Params, SNRangeGadget},
};

#[derive(Clone)]
pub struct Witness<F: PrimeField> {
    pub sn: F,
    pub h_range: F,
    pub range: (F, F),
    pub aux_h_range: Vec<Vec<bool>>,
}

impl<F: PrimeField> Default for Witness<F> {
    fn default() -> Self {
        Self {
            sn: Default::default(),
            h_range: Default::default(),
            range: Default::default(),
            aux_h_range: HPrime::EXTENSIONS.iter().map(|(n, _, _)| vec![false; *n]).collect(),
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
        let Witness { sn, h_range, range, aux_h_range } = w;

        let sn = FpVar::new_witness(cs.clone(), || Ok(sn))?;
        let h_range = FpVar::new_witness(cs.clone(), || Ok(h_range))?;
        let range = (
            FpVar::new_witness(cs.clone(), || Ok(range.0))?,
            FpVar::new_witness(cs.clone(), || Ok(range.1))?,
        );
        let aux_h_range = aux_h_range
            .iter()
            .map(|x| Vec::new_witness(cs.clone(), || Ok(x.clone())))
            .collect::<Result<Vec<_>, _>>()?;

        sn.enforce_cmp_unchecked(&range.0, Ordering::Greater, false)?;
        sn.enforce_cmp_unchecked(&range.1, Ordering::Less, false)?;
        h_range.enforce_equal(&SNRangeGadget::h_range_gen::<_, _, W>(pp, range, &aux_h_range)?)?;

        println!("{}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalSerialize;
    use num::bigint::RandBigInt;
    use rand::thread_rng;

    use super::*;
    use crate::{
        lego::{
            create_random_proof_incl_cp_link, generate_random_parameters_incl_cp_link,
            prepare_verifying_key, verify_proof_incl_cp_link,
        },
        protocols::{SNRange, SN},
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let (ask, _) = secp256k1::Secp256k1::new().generate_keypair(rng);

        let rho_sn = Fr::rand(rng);

        let sn = SN::sn_gen(pp, &ask, rho_sn);
        let lb = rng.gen_biguint_below(&sn.into()).into();
        let ub = rng.gen_biguint_range(&sn.into(), &Fr::MODULUS_MINUS_ONE_DIV_TWO.into()).into();
        let (h_range, aux_range) = SNRange::h_range_gen(pp, (lb, ub));

        let r_sn = Fr::rand(rng);
        let r_h_range = Fr::rand(rng);

        let w = Witness { sn, h_range, range: (lb, ub), aux_h_range: aux_range };
        let link_v = vec![r_sn, r_h_range];

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
        let r_h_range = Fr::rand(rng);

        let link_v = vec![r_sn, r_h_range];

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
        let lb = { rng.gen_biguint_below(&sn.into()).into() };
        let ub =
            { rng.gen_biguint_range(&sn.into(), &Fr::MODULUS_MINUS_ONE_DIV_TWO.into()).into() };
        let (h_range, aux_range) = SNRange::h_range_gen(pp, (lb, ub));

        let r_sn = Fr::rand(rng);
        let r_h_range = Fr::rand(rng);

        let w = Witness { sn, h_range, range: (lb, ub), aux_h_range: aux_range };
        let link_v = vec![r_sn, r_h_range];

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
        let lb = { rng.gen_biguint_below(&sn.into()).into() };
        let ub =
            { rng.gen_biguint_range(&sn.into(), &Fr::MODULUS_MINUS_ONE_DIV_TWO.into()).into() };
        let (h_range, aux_range) = SNRange::h_range_gen(pp, (lb, ub));

        let r_sn = Fr::rand(rng);
        let r_h_range = Fr::rand(rng);

        let w = Witness { sn, h_range, range: (lb, ub), aux_h_range: aux_range };
        let link_v = vec![r_sn, r_h_range];

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
