//! An implementation of the [`LegoGroth16`] zkSNARK.
//! An implementation of the LegoGroth16, the [`LegoSNARK`] variant of [`Groth16`] zkSNARK proof system.
//!
//! [`LegoSNARK`]: https://eprint.iacr.org/2019/142.pdf
//! [`Groth16`]: https://eprint.iacr.org/2016/260.pdf
#![warn(unused, nonstandard_style)]
#![allow(clippy::many_single_char_names, clippy::op_ref)]
#![forbid(unsafe_code)]

// #[macro_use]
// extern crate bench_utils;

#[cfg(feature = "r1cs")]
#[macro_use]
extern crate derivative;

/// Reduce an R1CS instance to a *Quadratic Arithmetic Program* instance.
pub(crate) mod r1cs_to_qap;

/// Data structures used by the prover, verifier, and generator.
pub mod data_structures;

/// Generate public parameters for the Groth16 zkSNARK construction.
pub mod generator;

/// Create proofs for the Groth16 zkSNARK construction.
pub mod prover;

/// Verify proofs for the Groth16 zkSNARK construction.
pub mod verifier;

pub mod link;

use ark_std::vec::Vec;

/// Constraints for the Groth16 verifier.
// Cannot yet create a LegoGroth16 gadget (for recursive proof) so commenting it out.
// #[cfg(feature = "r1cs")]
// pub mod constraints;
pub use self::{data_structures::*, generator::*, prover::*, r1cs_to_qap::*, verifier::*};
