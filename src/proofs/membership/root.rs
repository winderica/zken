use ark_ec::pairing::Pairing;
use ethers::prelude::k256::sha2::{Digest, Sha256};
use num::{
    bigint::{RandBigInt, ToBigInt},
    BigInt, BigUint, One, Signed,
};
use rand::thread_rng;
use serde::{Deserialize, Serialize};

use crate::{
    constants::{λ_n, λ_s, λ_z, μ},
    primitives::accumulator,
    protocols::Params,
    utils::Mod,
};

pub struct Statement<'a> {
    pub c_e: &'a BigUint,
    pub a: &'a BigUint,
}

pub struct Witness<'a> {
    pub w: &'a BigUint,
    pub e: &'a BigInt,
    pub r: &'a BigInt,
}

#[derive(Serialize, Deserialize)]
pub struct Proof {
    pub c_w: BigUint,
    pub c_r: BigUint,
    pub α_1: BigUint,
    pub α_2: BigUint,
    pub α_3: BigUint,
    pub α_4: BigUint,
    pub s_e: BigInt,
    pub s_r: BigInt,
    pub s_r_2: BigInt,
    pub s_r_3: BigInt,
    pub s_β: BigInt,
    pub s_δ: BigInt,
}

fn challenge(
    c_e: &BigUint,
    a: &BigUint,
    α_1: &BigUint,
    α_2: &BigUint,
    α_3: &BigUint,
    α_4: &BigUint,
) -> BigUint {
    BigUint::from_bytes_be(&Sha256::digest(
        [c_e, a, α_1, α_2, α_3, α_4]
            .iter()
            .flat_map(|i| {
                let mut i = i.to_bytes_be();
                i.resize(λ_n / 8, 0);
                i
            })
            .collect::<Vec<_>>(),
    )) % (BigUint::one() << λ_s)
}

pub fn prove<E: Pairing>(pp: &Params<E>, s: &Statement, w: Witness) -> Proof {
    let rng = &mut thread_rng();

    let accumulator::Parameters { g, h, n } = &pp.r;
    let Statement { c_e, a } = s;
    let Witness { e, r, w } = w;

    let (r_2, r_3) = {
        let bound = (n / 4u8).into();
        (rng.gen_bigint_range(&-&bound, &bound), rng.gen_bigint_range(&-&bound, &bound))
    };

    let c_w = BigUint::commit(&[w, h], &[&BigInt::one(), &r_2], n);
    let c_r = BigUint::commit(&[g, h], &[&r_2, &r_3], n);

    let r_e = {
        let bound = BigInt::from(2i8).pow(λ_z + λ_s + μ);
        rng.gen_bigint_range(&-&bound, &bound)
    };

    let (r_r, r_r_2, r_r_3) = {
        let bound = (n / 4u8).to_bigint().unwrap() * BigInt::from(2i8).pow(λ_z + λ_s);
        (
            rng.gen_bigint_range(&-&bound, &bound),
            rng.gen_bigint_range(&-&bound, &bound),
            rng.gen_bigint_range(&-&bound, &bound),
        )
    };

    let (r_β, r_δ) = {
        let bound = (n / 4u8).to_bigint().unwrap() * BigInt::from(2i8).pow(λ_z + λ_s + μ);
        (rng.gen_bigint_range(&-&bound, &bound), rng.gen_bigint_range(&-&bound, &bound))
    };

    let α_1 = BigUint::commit(&[g, h], &[&r_e, &r_r], n);
    let α_2 = BigUint::commit(&[g, h], &[&r_r_2, &r_r_3], n);
    let α_3 = BigUint::commit(&[&c_w, h], &[&r_e, &-&r_β], n);
    let α_4 = BigUint::commit(&[&c_r, g, h], &[&r_e, &-&r_β, &-&r_δ], n);

    let c: &BigInt = &challenge(c_e, a, &α_1, &α_2, &α_3, &α_4).into();

    let s_e = r_e - c * e;
    let s_r = r_r - c * r;
    let s_r_2 = r_r_2 - c * &r_2;
    let s_r_3 = r_r_3 - c * &r_3;
    let s_β = r_β - c * e * r_2;
    let s_δ = r_δ - c * e * r_3;

    Proof { c_w, c_r, α_1, α_2, α_3, α_4, s_e, s_r, s_r_2, s_r_3, s_β, s_δ }
}

pub fn verify<E: Pairing>(pp: &Params<E>, s: &Statement, π: &Proof) -> bool {
    let accumulator::Parameters { g, h, n } = &pp.r;
    let Statement { c_e, a } = s;
    let Proof { c_w, c_r, α_1, α_2, α_3, α_4, s_e, s_r, s_r_2, s_r_3, s_β, s_δ } = π;

    let c = &challenge(c_e, a, α_1, α_2, α_3, α_4).into();

    let res = true;
    res && *α_1 == BigUint::commit(&[c_e, g, h], &[c, s_e, s_r], n)
        && *α_2 == BigUint::commit(&[c_r, g, h], &[c, s_r_2, s_r_3], n)
        && *α_3 == BigUint::commit(&[a, c_w, h], &[c, s_e, &-s_β], n)
        && *α_4 == BigUint::commit(&[c_r, g, h], &[s_e, &-s_β, &-s_δ], n)
        && s_e.abs() <= BigInt::from(2i8).pow(λ_z + λ_s + μ + 1)
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;

    use super::*;

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let r = &rng.gen_bigint(123);
        let w = &rng.gen_biguint(123);
        let e = &rng.gen_bigint(123);

        let a = &w.mod_exp(e, &pp.r.n);

        let c_e = &(pp.r.g.mod_exp(e, &pp.r.n) * pp.r.h.mod_exp(r, &pp.r.n) % &pp.r.n);

        let s = Statement { c_e, a };

        let w = Witness { w, r, e };

        let π = prove(pp, &s, w);
        assert!(verify(pp, &s, &π));
    }
}
