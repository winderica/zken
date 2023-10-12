use ark_ff::PrimeField;

pub mod range;
pub mod sum;

pub trait PourCustomWitness<F: PrimeField, const M: usize, const N: usize>: Default {
    fn new(inputs: [F; M], outputs: [F; N]) -> Self;
}

pub trait RevealCustomWitness<F: PrimeField>: Default {
    fn new(value: F) -> Self;
}
