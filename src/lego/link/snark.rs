//! zkSNARK for Linear Subspaces as defined in appendix D of the paper.
//! Use to prove knowledge of openings of multiple Pedersen commitments. Can also prove knowledge
//! and equality of committed values in multiple commitments. Note that this SNARK requires a trusted
//! setup as the key generation creates a trapdoor.

use std::ops::Mul;

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{One, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{marker::PhantomData, ops::Neg, rand::Rng, vec::Vec};

use super::utils::*;

/// Public params
#[derive(Clone, Default, PartialEq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PP<E: Pairing> {
    pub l: usize, // # of rows
    pub t: usize, // # of cols
    pub g1: E::G1Affine,
    pub g2: E::G2Affine,
}

impl<E: Pairing> PP<E> {
    pub fn new(l: usize, t: usize, g1: E::G1Affine, g2: E::G2Affine) -> Self {
        PP { l, t, g1, g2 }
    }
}

/// Evaluation key
#[derive(Clone, Default, PartialEq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EK<E: Pairing> {
    pub p: Vec<E::G1Affine>,
}

/// Verification key
#[derive(Clone, Default, PartialEq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct VK<E: Pairing> {
    pub c: Vec<E::G2Affine>,
    pub a: E::G2Affine,
}

pub trait SubspaceSnark {
    type KMtx;
    type InVec;
    type OutVec;

    type PP;

    type EK;
    type VK;

    type Proof;

    fn keygen<R: Rng>(rng: &mut R, pp: &Self::PP, m: &Self::KMtx) -> (Self::EK, Self::VK);
    fn prove(pp: &Self::PP, ek: &Self::EK, w: &[Self::InVec]) -> Self::Proof;
    fn verify(pp: &Self::PP, vk: &Self::VK, y: &[Self::OutVec], pi: &Self::Proof) -> bool;
}

pub struct PESubspaceSnark<PE: Pairing> {
    pairing_engine_type: PhantomData<PE>,
}

// NB: Now the system is for y = Mx
impl<PE: Pairing> SubspaceSnark for PESubspaceSnark<PE> {
    type KMtx = SparseMatrix<PE::G1Affine>;
    type InVec = PE::ScalarField;
    type OutVec = PE::G1Affine;

    type PP = PP<PE>;

    type EK = EK<PE>;
    type VK = VK<PE>;

    type Proof = PE::G1Affine;

    /// Matrix should be such that a column will have more than 1 non-zero item only if those values
    /// are equal. Eg for matrix below, h2 and h3 commit to same value
    /// h1, 0, 0, 0
    /// 0, h2, 0, 0
    /// 0, h3, h4, 0
    fn keygen<R: Rng>(rng: &mut R, pp: &Self::PP, m: &Self::KMtx) -> (Self::EK, Self::VK) {
        // `k` is the trapdoor
        let mut k: Vec<PE::ScalarField> = Vec::with_capacity(pp.l);
        for _ in 0..pp.l {
            k.push(PE::ScalarField::rand(rng));
        }

        let a = PE::ScalarField::rand(rng);

        let p = SparseLinAlgebra::<PE>::sparse_vector_matrix_mult(&k, m);

        let c = scale_vector::<PE>(&a, &k);
        let ek = EK::<PE> { p };
        let vk = VK::<PE> {
            c: multiples_of_g::<PE::G2Affine>(&pp.g2, &c),
            a: pp.g2.mul(a).into_affine(),
        };
        (ek, vk)
    }

    fn prove(pp: &Self::PP, ek: &Self::EK, w: &[Self::InVec]) -> Self::Proof {
        assert!(pp.t >= w.len());
        inner_product::<PE>(w, &ek.p)
    }

    fn verify(pp: &Self::PP, vk: &Self::VK, x: &[Self::OutVec], pi: &Self::Proof) -> bool {
        assert_eq!(pp.l, x.len());

        let mut l = x.to_vec();
        l.push(*pi);
        let mut r = vk.c.to_vec();
        r.push(vk.a.into_group().neg().into_affine());
        PE::multi_pairing(l, r).0.is_one()
    }
}
