use std::cmp::Ordering;

use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use serde::{Deserialize, Serialize};

use super::RevealCustomWitness;
use crate::{proofs::Circuit, protocols::Params, utils::num_constraints};

#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Statement<F: PrimeField> {
    pub l: F,
    pub u: F,
}

#[derive(Default, Clone)]
pub struct Witness<F: PrimeField> {
    pub v: F,
}

impl<F: PrimeField> RevealCustomWitness<F> for Witness<F> {
    fn new(value: F) -> Self {
        Self { v: value }
    }
}

pub struct RangeCircuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub s: Statement<E::ScalarField>,
    pub w: Witness<E::ScalarField>,
}

impl<'a, E: Pairing> Circuit<'a, E> for RangeCircuit<'a, E> {
    const NUM_COMMIT_WITNESSES: usize = 1;
    const NAME: &'static str = "Range";
    type Statement = Statement<E::ScalarField>;
    type Witness = Witness<E::ScalarField>;

    fn new(pp: &'a Params<E>, s: Self::Statement, w: Self::Witness) -> Self {
        Self { pp, s, w }
    }

    fn inputize(s: &Self::Statement) -> Vec<E::ScalarField> {
        vec![s.l, s.u]
    }
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for RangeCircuit<'a, E> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<E::ScalarField>,
    ) -> Result<(), SynthesisError> {
        let Self { s, w, .. } = self;
        let Statement { l, u } = s;
        let Witness { v } = w;

        let v = FpVar::new_witness(cs.clone(), || Ok(v))?;

        println!("Shape check: {}", cs.num_constraints());

        println!(
            "Range check: {}",
            num_constraints(&cs, || {
                v.enforce_cmp(&FpVar::new_input(cs.clone(), || Ok(l))?, Ordering::Greater, true)?;
                v.enforce_cmp(&FpVar::new_input(cs.clone(), || Ok(u))?, Ordering::Less, false)
            })?
        );

        println!("Total: {}", cs.num_constraints());

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
    use crate::proofs::ProofSystem;

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

        let link_v = [r_v];

        let crs = ProofSystem::<_, RangeCircuit<_>>::setup(&pp, rng).unwrap();

        println!("{}", crs.pk.compressed_size());

        let proof_link = crs.prove(s.clone(), w, &link_v, rng).unwrap();

        println!("{}", proof_link.compressed_size());

        assert!(crs.verify(&s, &proof_link).unwrap());

        crs.print_on_chain(&s, &proof_link);
    }

    #[bench]
    fn bench_keygen(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        b.iter(|| ProofSystem::<_, RangeCircuit<_>>::setup(&pp, rng).unwrap());
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

        let link_v = [r_v];

        let crs = ProofSystem::<_, RangeCircuit<_>>::setup(&pp, rng).unwrap();

        b.iter(|| crs.prove(s.clone(), w.clone(), &link_v, rng).unwrap());
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

        let link_v = [r_v];

        let crs = ProofSystem::<_, RangeCircuit<_>>::setup(&pp, rng).unwrap();

        let proof_link = crs.prove(s.clone(), w, &link_v, rng).unwrap();

        b.iter(|| crs.verify(&s, &proof_link).unwrap())
    }
}
