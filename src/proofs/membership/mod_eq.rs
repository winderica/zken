use std::ops::Mul;

use ark_ec::{pairing::Pairing, CurveGroup, AffineRepr};
use ark_ff::{PrimeField, UniformRand};
use ark_serialize::{CanonicalSerialize, buffer_byte_size};
use ethers::prelude::k256::sha2::{Digest, Sha256};
use num::{
    bigint::{RandBigInt, ToBigInt},
    BigInt, BigUint, One,
};
use rand::thread_rng;
use serde::{Deserialize, Serialize};

use crate::{
    constants::{λ_n, λ_s, λ_z, μ},
    primitives::accumulator,
    protocols::Params,
    utils::Mod,
};

pub struct Statement<'a, E: Pairing> {
    pub c_e_n: &'a BigUint,
    pub c_e_q: &'a E::G1Affine,
}

pub struct Witness<'a, E: Pairing> {
    pub e: &'a BigInt,
    pub r_n: &'a BigInt,
    pub r_q: &'a E::ScalarField,
}

#[derive(Serialize, Deserialize)]
pub struct Proof<E: Pairing> {
    pub α_1: BigUint,
    pub α_2: E::G1Affine,
    pub s_e: BigInt,
    pub s_r_n: BigInt,
    pub s_r_q: E::ScalarField,
}

fn challenge<E: Pairing>(
    c_e_n: &BigUint,
    c_e_q: &E::G1Affine,
    α_1: &BigUint,
    α_2: &E::G1Affine,
) -> BigUint {
    let l = buffer_byte_size(E::BaseField::MODULUS_BIT_SIZE as usize);
    let mut v_n = c_e_n.to_bytes_be();
    v_n.resize(λ_n / 8, 0);
    let mut v_q = vec![0; l * 2];
    let (x, y) = c_e_q.xy().unwrap();
    x.serialize_uncompressed(&mut v_q[..l]).unwrap();
    y.serialize_uncompressed(&mut v_q[l..]).unwrap();
    let mut v_1 = α_1.to_bytes_be();
    v_1.resize(λ_n / 8, 0);
    let mut v_2 = vec![0; l * 2];
    let (x, y) = α_2.xy().unwrap();
    x.serialize_uncompressed(&mut v_2[..l]).unwrap();
    y.serialize_uncompressed(&mut v_2[l..]).unwrap();

    BigUint::from_bytes_be(&Sha256::digest([v_n, v_q, v_1, v_2].concat()))
        % (BigUint::one() << λ_s)
}

pub fn prove<E: Pairing>(pp: &Params<E>, s: &Statement<E>, w: Witness<E>) -> Proof<E> {
    let rng = &mut thread_rng();

    let accumulator::Parameters { g, h, n } = &pp.r;
    let Statement { c_e_n, c_e_q } = s;
    let Witness { e, r_n, r_q } = w;

    let q: BigUint = <E::ScalarField as PrimeField>::MODULUS.into();
    let q: BigInt = q.into();

    let r_e_n = {
        let bound = BigInt::from(2i8).pow(λ_z + λ_s + μ);
        rng.gen_bigint_range(&-&bound, &bound)
    };
    let r_e_q = &r_e_n % &q;
    let r_e_q = ((r_e_q + &q) % &q).to_biguint().unwrap();
    let r_e_q = E::ScalarField::from(r_e_q);

    let r_r_n = {
        let bound = (n / 4u8).to_bigint().unwrap() * BigInt::from(2i8).pow(λ_z + λ_s);
        rng.gen_bigint_range(&-&bound, &bound)
    };

    let r_r_q = E::ScalarField::rand(rng);

    let α_1 = BigUint::commit(&[g, h], &[&r_e_n, &r_r_n], n);
    let α_2 = (pp.c.g.mul(r_e_q) + pp.c.h.mul(r_r_q)).into_affine();

    let c_n = challenge::<E>(c_e_n, c_e_q, &α_1, &α_2);
    let c_q = E::ScalarField::from(c_n.clone());
    let c_n: &BigInt = &c_n.into();

    let s_e = r_e_n - c_n * e;
    let s_r_n = r_r_n - c_n * r_n;
    let s_r_q = r_r_q - c_q * r_q;

    Proof { α_1, α_2, s_e, s_r_n, s_r_q }
}

pub fn verify<E: Pairing>(pp: &Params<E>, s: &Statement<E>, π: &Proof<E>) -> bool {
    let Proof { α_1, α_2, s_e, s_r_n, s_r_q } = π;
    let accumulator::Parameters { g, h, n } = &pp.r;
    let Statement { c_e_n, c_e_q } = s;

    let q: BigUint = <E::ScalarField as PrimeField>::MODULUS.into();
    let q: BigInt = q.into();

    let s_e_n = s_e % &q;
    let s_e_n = ((s_e_n + &q) % &q).to_biguint().unwrap();
    let s_e_n = E::ScalarField::from(s_e_n);

    let c_n = challenge::<E>(c_e_n, c_e_q, α_1, α_2);
    let c_q = E::ScalarField::from(c_n.clone());
    let c_n: &BigInt = &c_n.into();

    let res = true;
    res && *α_1 == BigUint::commit(&[c_e_n, g, h], &[c_n, s_e, s_r_n], n)
        && *α_2 == (c_e_q.mul(c_q) + pp.c.g.mul(s_e_n) + pp.c.h.mul(*s_r_q)).into_affine()
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ff::UniformRand;

    use super::*;

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let e_q = Fr::rand(rng);
        let r_n = &rng.gen_bigint(123);

        let e_n: BigUint = e_q.into();
        let e: &BigInt = &e_n.into();

        let c_e_n = &BigUint::commit(&[&pp.r.g, &pp.r.h], &[e, r_n], &pp.r.n);
        let r_q = Fr::rand(rng);
        let c_e_q = &(pp.c.g.mul(e_q) + pp.c.h.mul(r_q)).into_affine();

        let s = Statement { c_e_n, c_e_q };

        let w = Witness { r_n, e, r_q: &Into::<BigUint>::into(r_q).into() };

        let π = prove(pp, &s, w);

        assert!(verify(pp, &s, &π));
    }
}
