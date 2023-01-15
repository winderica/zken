use super::link::{EK, PP, VK};
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::{UniformRand};
use ark_serialize::*;
use ark_std::{
    vec::Vec,
};
use rand::Rng;
use serde::{Serialize, Deserialize};
use serde_with::serde_as;

/// A proof in the Groth16 SNARK
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<E: Pairing> {
    /// The `A` element in `G1`.
    pub a: E::G1Affine,
    /// The `B` element in `G2`.
    pub b: E::G2Affine,
    /// The `C` element in `G1`.
    pub c: E::G1Affine,
    /// The `D` element in `G1`. Commits to a subset of private inputs of the circuit
    pub d: E::G1Affine,
    /// The `delta'` element in `G2`.
    pub delta_prime: E::G2Affine,
}

/// A proof in the Groth16 SNARK with CP_link proof
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProofWithLink<E: Pairing> {
    pub groth16_proof: Proof<E>,
    /// cp_{link}
    pub link_d: Vec<E::G1Affine>,
    /// proof of commitment opening equality between `cp_{link}` and `d`
    pub link_pi: E::G1Affine,
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// A verification key in the Groth16 SNARK.
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifyingKey<E: Pairing> {
    /// The `alpha * G`, where `G` is the generator of `E::G1`.
    pub alpha_g1: E::G1Affine,
    /// The `alpha * H`, where `H` is the generator of `E::G2`.
    pub beta_g2: E::G2Affine,
    /// The `gamma * H`, where `H` is the generator of `E::G2`.
    pub gamma_g2: E::G2Affine,
    /// The `delta * H`, where `H` is the generator of `E::G2`.
    pub delta_g2: E::G2Affine,
    /// The `gamma^{-1} * (beta * a_i + alpha * b_i + c_i) * H`, where `H` is the generator of `E::G1`.
    pub gamma_abc_g1: Vec<E::G1Affine>,
    /// The element `eta*gamma^-1 * G` in `E::G1`.
    pub eta_gamma_inv_g1: E::G1Affine,
    /// No of witness to commit
    pub commit_witness_count: usize,
    /// The element `zt*delta^{-1}` in `E::G1` 
    pub zt_delta_g1: E::G1Affine,
}

/// A verification key in the Groth16 SNARK with CP_link verification parameters
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct VerifyingKeyWithLink<E: Pairing> {
    pub groth16_vk: VerifyingKey<E>,
    /// Public parameters of the Subspace Snark
    pub link_pp: PP<E>,
    /// Commitment key of the link commitment cp_link
    pub link_bases: (E::G1Affine, E::G1Affine),
    /// Verification key of the Subspace Snark
    pub link_vk: VK<E>,
}

/// Preprocessed verification key parameters that enable faster verification
/// at the expense of larger size in memory.
#[derive(Clone, Debug, PartialEq)]
pub struct PreparedVerifyingKey<E: Pairing> {
    /// The unprepared verification key.
    pub vk: VerifyingKey<E>,
    /// The element `e(alpha * G, beta * H)` in `E::GT`.
    pub alpha_g1_beta_g2: E::TargetField,
    /// The element `- gamma * H` in `E::G2`, prepared for use in pairings.
    pub gamma_g2_neg_pc: E::G2Prepared,
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// The common elements for Proving Key for with and without CP_link
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProvingKeyCommon<E: Pairing> {
    /// The element `beta * G` in `E::G1`.
    pub beta_g1: E::G1Affine,
    /// The element `delta * G` in `E::G1`.
    pub delta_g1: E::G1Affine,
    /// The element `eta*delta^-1 * G` in `E::G1`.
    pub eta_delta_inv_g1: E::G1Affine,
    /// The elements `a_i * G` in `E::G1`.
    pub a_query: Vec<E::G1Affine>,
    /// The elements `b_i * G` in `E::G1`.
    pub b_g1_query: Vec<E::G1Affine>,
    /// The elements `b_i * H` in `E::G2`.
    pub b_g2_query: Vec<E::G2Affine>,
    /// The elements `h_i * G` in `E::G1`.
    pub h_query: Vec<E::G1Affine>,
    /// The elements `l_i * G` in `E::G1`.
    pub l_query: Vec<E::G1Affine>,
}

/// The prover key for for the Groth16 zkSNARK.
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProvingKey<E: Pairing> {
    /// The underlying verification key.
    pub vk: VerifyingKey<E>,
    pub common: ProvingKeyCommon<E>,
}

/// The prover key for for the Groth16 zkSNARK with CP_link parameters
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProvingKeyWithLink<E: Pairing> {
    /// The underlying verification key.
    pub vk: VerifyingKeyWithLink<E>,
    pub common: ProvingKeyCommon<E>,
    /// Evaluation key of cp_{link}
    pub link_ek: EK<E>,
}

/// Public parameters for CP link
#[serde_as]
#[derive(Clone, Debug, PartialEq, CanonicalSerialize, CanonicalDeserialize, Serialize, Deserialize)]
pub struct LinkPublicGenerators<E: Pairing> {
    #[serde_as(as = "crate::utils::SerdeAs")]
    pub g: E::G1Affine,
    #[serde_as(as = "crate::utils::SerdeAs")]
    pub h: E::G1Affine,
    #[serde_as(as = "crate::utils::SerdeAs")]
    pub g1: E::G1Affine,
    #[serde_as(as = "crate::utils::SerdeAs")]
    pub g2: E::G2Affine,
}

impl<E: Pairing> LinkPublicGenerators<E> {
    pub fn new<R: Rng>(rng: &mut R) -> Self {
        Self {
            g: E::G1::rand(rng).into_affine(),
            h: E::G1::rand(rng).into_affine(),
            g1: E::G1::rand(rng).into_affine(),
            g2: E::G2::rand(rng).into_affine(),
        }
    }
}
