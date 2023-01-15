use ark_ec::pairing::Pairing;
use num::{BigInt, BigUint};
use serde::{Deserialize, Serialize};

use super::{coprime, mod_eq, root};
use crate::protocols::Params;

#[derive(Serialize, Deserialize)]
pub struct Statement<E: Pairing> {
    pub a_mem: BigUint,
    pub a_nonmem: BigUint,
    pub c_e_n: BigUint,
    pub c_e_q: E::G1Affine,
}

pub struct Witness<E: Pairing> {
    pub w_mem: BigUint,
    pub w_nonmem: BigUint,
    pub e: BigInt,
    pub r_n: BigInt,
    pub r_q: E::ScalarField,
}

pub type Proof<E> = (root::Proof, coprime::Proof, mod_eq::Proof<E>);

pub fn prove<E: Pairing>(pp: &Params<E>, s: &Statement<E>, w: &Witness<E>) -> Proof<E> {
    let Statement { a_mem, a_nonmem, c_e_n, c_e_q } = s;
    let Witness { w_mem, w_nonmem, e, r_n, r_q } = w;
    (
        root::prove(
            pp,
            &root::Statement { c_e: c_e_n, a: a_mem },
            root::Witness { w: w_mem, e, r: r_n },
        ),
        coprime::prove(
            pp,
            &coprime::Statement { c_e: c_e_n, a: a_nonmem },
            coprime::Witness { w: w_nonmem, e, r: r_n },
        ),
        mod_eq::prove(pp, &mod_eq::Statement { c_e_n, c_e_q }, mod_eq::Witness { e, r_n, r_q }),
    )
}

pub fn verify<E: Pairing>(pp: &Params<E>, s: &Statement<E>, π: &Proof<E>) -> bool {
    let Statement { a_mem, a_nonmem, c_e_n, c_e_q } = s;
    root::verify(pp, &root::Statement { c_e: c_e_n, a: a_mem }, &π.0)
        && coprime::verify(pp, &coprime::Statement { c_e: c_e_n, a: a_nonmem }, &π.1)
        && mod_eq::verify(pp, &mod_eq::Statement { c_e_n, c_e_q }, &π.2)
}

#[cfg(test)]
mod tests {
    use std::ops::Mul;

    use ark_bn254::{Bn254, Fr};
    use ark_ec::CurveGroup;
    use ark_ff::UniformRand;
    use num::bigint::RandBigInt;
    use num_prime::RandPrime;
    use rand::thread_rng;

    use super::*;
    use crate::utils::Mod;

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let w_mem = rng.gen_biguint(123);
        let w_nonmem = rng.gen_biguint(456);
        let e: BigUint = rng.gen_prime(123, None);
        let r_q = Fr::rand(rng);
        let r_n = rng.gen_bigint(123);

        let a_mem = w_mem.mod_exp(&e, &pp.r.n);
        let a_nonmem = pp.r.g.mod_exp(&w_nonmem, &pp.r.n);

        let c_e_n = BigUint::commit(&[&pp.r.g, &pp.r.h], &[&e.clone().into(), &r_n], &pp.r.n);
        let c_e_q = (pp.c.g.mul(Fr::from(e.clone())) + pp.c.h.mul(r_q)).into_affine();

        let s = Statement { c_e_n, c_e_q, a_mem, a_nonmem };

        let w =
            Witness { w_mem, w_nonmem, r_n, e: e.into(), r_q: Into::<BigUint>::into(r_q).into() };

        let π = prove(pp, &s, &w);
        assert!(verify(pp, &s, &π));
    }
}
