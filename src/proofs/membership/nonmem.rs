use ark_ec::pairing::Pairing;
use num::{BigInt, BigUint};
use serde::{Deserialize, Serialize};

use super::{coprime, mod_eq};
use crate::protocols::Params;

#[derive(Serialize, Deserialize)]
pub struct Statement<E: Pairing> {
    pub a: BigUint,
    pub c_e_n: BigUint,
    pub c_e_q: E::G1Affine,
}

pub struct Witness<E: Pairing> {
    pub w: BigUint,
    pub e: BigInt,
    pub r_n: BigInt,
    pub r_q: E::ScalarField,
}

pub type Proof<E> = (coprime::Proof, mod_eq::Proof<E>);

pub fn prove<E: Pairing>(pp: &Params<E>, s: &Statement<E>, w: &Witness<E>) -> Proof<E> {
    let Statement { a, c_e_n, c_e_q } = s;
    let Witness { w, e, r_n, r_q } = w;
    (
        coprime::prove(
            pp,
            &coprime::Statement { c_e: c_e_n, a },
            coprime::Witness { w, e, r: r_n },
        ),
        mod_eq::prove(pp, &mod_eq::Statement { c_e_n, c_e_q }, mod_eq::Witness { e, r_n, r_q }),
    )
}

pub fn verify<E: Pairing>(pp: &Params<E>, s: &Statement<E>, π: &Proof<E>) -> bool {
    let Statement { a, c_e_n, c_e_q } = s;
    coprime::verify(pp, &coprime::Statement { c_e: c_e_n, a }, &π.0)
        && mod_eq::verify(pp, &mod_eq::Statement { c_e_n, c_e_q }, &π.1)
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

        let w = rng.gen_biguint(456);
        let e: BigUint = rng.gen_prime(123, None);
        let r_q = Fr::rand(rng);
        let r_n = rng.gen_bigint(123);

        let a = pp.r.g.mod_exp(&w, &pp.r.n);

        let c_e_n = BigUint::commit(&[&pp.r.g, &pp.r.h], &[&e.clone().into(), &r_n], &pp.r.n);
        let c_e_q = (pp.c.g.mul(Fr::from(e.clone())) + pp.c.h.mul(r_q)).into_affine();

        let s = Statement { c_e_n, c_e_q, a };

        let w = Witness { w, r_n, e: e.into(), r_q: Into::<BigUint>::into(r_q).into() };

        let π = prove(pp, &s, &w);
        assert!(verify(pp, &s, &π));
    }
}
