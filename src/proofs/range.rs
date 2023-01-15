use std::cmp::Ordering;

use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use serde::{Deserialize, Serialize};

use crate::protocols::Params;

#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Statement<F: PrimeField> {
    pub l: F,
    pub u: F,
}

impl<F: PrimeField> Statement<F> {
    pub fn inputize(&self) -> Vec<F> {
        vec![self.l, self.u]
    }
}

#[derive(Default, Clone)]
pub struct Witness<F: PrimeField> {
    pub v: F,
}

pub struct Circuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub s: Statement<E::ScalarField>,
    pub w: Witness<E::ScalarField>,
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for Circuit<'a, E> {
    fn generate_constraints(self, cs: ConstraintSystemRef<E::ScalarField>) -> Result<(), SynthesisError> {
        let Self { s, w, .. } = self;
        let Statement { l, u } = s;
        let Witness { v } = w;

        let v = FpVar::new_witness(cs.clone(), || Ok(v))?;

        v.enforce_cmp(&FpVar::new_input(cs.clone(), || Ok(l))?, Ordering::Greater, true)?;
        v.enforce_cmp(&FpVar::new_input(cs.clone(), || Ok(u))?, Ordering::Less, false)?;

        println!("{}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalSerialize;
    use rand::{thread_rng, Rng};

    use super::*;
    use crate::lego::{
        create_random_proof_incl_cp_link, generate_random_parameters_incl_cp_link,
        prepare_verifying_key, verify_proof_incl_cp_link,
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let l = Fr::from(1234);
        let u = Fr::from(123456789);

        let v = Fr::from(rng.gen_range(1234..123456789));

        let r_v = Fr::rand(rng);

        let s = Statement { l, u };
        let w = Witness { v };
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

        assert!(verify_proof_incl_cp_link(&pvk_link, &params_link.vk, &proof_link, &public_input).unwrap());
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

        let l = Fr::from(1234);
        let u = Fr::from(123456789);

        let v = Fr::from(rng.gen_range(1234..123456789));

        let r_v = Fr::rand(rng);

        let s = Statement { l, u };
        let w = Witness { v };

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

        let l = Fr::from(1234);
        let u = Fr::from(123456789);

        let v = Fr::from(rng.gen_range(1234..123456789));

        let r_v = Fr::rand(rng);

        let s = Statement { l, u };
        let w = Witness { v };
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
