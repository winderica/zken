use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::EqGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

use super::PourCustomWitness;
use crate::{proofs::Circuit, protocols::Params, utils::num_constraints};

#[derive(Clone)]
pub struct Witness<F: PrimeField, const M: usize, const N: usize> {
    pub inputs: [F; M],
    pub outputs: [F; N],
}

impl<F: PrimeField, const M: usize, const N: usize> PourCustomWitness<F, M, N>
    for Witness<F, M, N>
{
    fn new(inputs: [F; M], outputs: [F; N]) -> Self {
        Self { inputs, outputs }
    }
}

impl<F: PrimeField, const M: usize, const N: usize> Default for Witness<F, M, N> {
    fn default() -> Self {
        Self { inputs: [F::default(); M], outputs: [F::default(); N] }
    }
}

pub struct SumCircuit<'a, E: Pairing, const M: usize, const N: usize> {
    pub pp: &'a Params<E>,
    pub w: Witness<E::ScalarField, M, N>,
}

impl<'a, E: Pairing, const M: usize, const N: usize> Circuit<'a, E> for SumCircuit<'a, E, M, N> {
    const NUM_COMMIT_WITNESSES: usize = M + N;
    const NAME: &'static str = "Sum";
    type Statement = ();
    type Witness = Witness<E::ScalarField, M, N>;

    fn new(pp: &'a Params<E>, _: Self::Statement, w: Self::Witness) -> Self {
        Self { pp, w }
    }

    fn inputize(_: &Self::Statement) -> Vec<E::ScalarField> {
        vec![]
    }
}

impl<'a, E: Pairing, const M: usize, const N: usize> ConstraintSynthesizer<E::ScalarField>
    for SumCircuit<'a, E, M, N>
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<E::ScalarField>,
    ) -> Result<(), SynthesisError> {
        let Self { w, .. } = self;
        let Witness { inputs, outputs } = w;

        let inputs = Vec::<FpVar<E::ScalarField>>::new_witness(cs.clone(), || Ok(inputs))?;
        let outputs = Vec::<FpVar<E::ScalarField>>::new_witness(cs.clone(), || Ok(outputs))?;

        println!("Shape check: {}", cs.num_constraints());

        println!(
            "Sum check: {}",
            num_constraints(&cs, || {
                inputs
                    .iter()
                    .sum::<FpVar<E::ScalarField>>()
                    .enforce_equal(&outputs.iter().sum::<FpVar<E::ScalarField>>())
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
    use rand::thread_rng;

    use super::*;
    use crate::proofs::ProofSystem;

    const M: usize = 5;
    const N: usize = 3;

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let inputs = [Fr::default(); M].map(|_| Fr::rand(rng));
        let mut outputs = [Fr::default(); N].map(|_| Fr::rand(rng));
        outputs[0] = inputs.iter().sum::<Fr>() - outputs.iter().skip(1).sum::<Fr>();

        let w = Witness { inputs, outputs };

        let link_v = [Fr::default(); M + N].map(|_| Fr::rand(rng));

        let crs = ProofSystem::<_, SumCircuit<_, M, N>>::setup(&pp, rng).unwrap();
        println!("{}", crs.pk.compressed_size());

        let proof_link = crs.prove((), w, &link_v, rng).unwrap();

        println!("{}", proof_link.compressed_size());

        assert!(crs.verify(&(), &proof_link).unwrap());

        crs.print_on_chain(&(), &proof_link);
    }

    #[bench]
    fn bench_keygen(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        b.iter(|| ProofSystem::<_, SumCircuit<_, M, N>>::setup(&pp, rng).unwrap());
    }

    #[bench]
    fn bench_prove(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let inputs = [Fr::default(); M].map(|_| Fr::rand(rng));
        let mut outputs = [Fr::default(); N].map(|_| Fr::rand(rng));
        outputs[0] = inputs.iter().sum::<Fr>() - outputs.iter().skip(1).sum::<Fr>();

        let w = Witness { inputs, outputs };

        let link_v = [Fr::default(); M + N].map(|_| Fr::rand(rng));

        let crs = ProofSystem::<_, SumCircuit<_, M, N>>::setup(&pp, rng).unwrap();

        b.iter(|| crs.prove((), w.clone(), &link_v, rng).unwrap());
    }

    #[bench]
    fn bench_verify(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let inputs = [Fr::default(); M].map(|_| Fr::rand(rng));
        let mut outputs = [Fr::default(); N].map(|_| Fr::rand(rng));
        outputs[0] = inputs.iter().sum::<Fr>() - outputs.iter().skip(1).sum::<Fr>();

        let w = Witness { inputs, outputs };

        let link_v = [Fr::default(); M + N].map(|_| Fr::rand(rng));

        let crs = ProofSystem::<_, SumCircuit<_, M, N>>::setup(&pp, rng).unwrap();

        let proof_link = crs.prove((), w, &link_v, rng).unwrap();

        b.iter(|| crs.verify(&(), &proof_link).unwrap())
    }
}
