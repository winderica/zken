use ark_ec::pairing::Pairing;
use ethers::prelude::k256::sha2::{Digest, Sha256};
use num::{
    bigint::{RandBigInt, ToBigInt},
    integer::ExtendedGcd,
    BigInt, BigUint, Integer, One, Signed,
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
    pub c_a: BigUint,
    pub c_r_a: BigUint,
    pub c_b: BigUint,
    pub c_ρ_b: BigUint,
    pub α_2: BigUint,
    pub α_3: BigUint,
    pub α_4: BigUint,
    pub α_5: BigUint,
    pub α_6: BigUint,
    pub α_7: BigUint,
    pub s_b: BigInt,
    pub s_e: BigInt,
    pub s_ρ_b: BigInt,
    pub s_r: BigInt,
    pub s_r_a: BigInt,
    pub s_rr_a: BigInt,
    pub s_ρρ_b: BigInt,
    pub s_β: BigInt,
    pub s_δ: BigInt,
}

fn challenge(
    c_e: &BigUint,
    a: &BigUint,
    α_2: &BigUint,
    α_3: &BigUint,
    α_4: &BigUint,
    α_5: &BigUint,
    α_6: &BigUint,
    α_7: &BigUint,
) -> BigUint {
    BigUint::from_bytes_be(&Sha256::digest(
        [c_e, a, α_2, α_3, α_4, α_5, α_6, α_7]
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

    let (d, b) = {
        let ExtendedGcd { gcd, x, y, .. } = e.extended_gcd(&w.to_bigint().unwrap());

        assert_eq!(gcd, BigInt::one());

        (pp.r.g.mod_exp(&x, &pp.r.n), y)
    };

    let (r_a, rr_a, ρ_b, ρρ_b) = {
        let bound = (n / 4u8).into();
        (
            rng.gen_bigint_range(&-&bound, &bound),
            rng.gen_bigint_range(&-&bound, &bound),
            rng.gen_bigint_range(&-&bound, &bound),
            rng.gen_bigint_range(&-&bound, &bound),
        )
    };

    let c_a = BigUint::commit(&[&d, h], &[&BigInt::one(), &r_a], n);
    let c_r_a = BigUint::commit(&[g, h], &[&r_a, &rr_a], n);
    let c_b = BigUint::commit(&[a, h], &[&b, &ρ_b], n);
    let c_ρ_b = BigUint::commit(&[g, h], &[&ρ_b, &ρρ_b], n);

    let (r_b, r_e) = {
        let bound = BigInt::from(2i8).pow(λ_z + λ_s + μ);
        (rng.gen_bigint_range(&-&bound, &bound), rng.gen_bigint_range(&-&bound, &bound))
    };
    let (r_ρ_b, r_r, r_r_a, r_rr_a, r_ρρ_b) = {
        let bound = (n / 4u8).to_bigint().unwrap() * BigInt::from(2i8).pow(λ_z + λ_s);
        (
            rng.gen_bigint_range(&-&bound, &bound),
            rng.gen_bigint_range(&-&bound, &bound),
            rng.gen_bigint_range(&-&bound, &bound),
            rng.gen_bigint_range(&-&bound, &bound),
            rng.gen_bigint_range(&-&bound, &bound),
        )
    };
    let (r_β, r_δ) = {
        let bound = (n / 4u8).to_bigint().unwrap() * BigInt::from(2i8).pow(λ_z + λ_s + μ);
        (rng.gen_bigint_range(&-&bound, &bound), rng.gen_bigint_range(&-&bound, &bound))
    };

    let α_2 = BigUint::commit(&[a, h], &[&r_b, &r_ρ_b], n);
    let α_3 = BigUint::commit(&[g, h], &[&r_e, &r_r], n);
    let α_4 = BigUint::commit(&[g, h], &[&r_r_a, &r_rr_a], n);
    let α_5 = BigUint::commit(&[&c_a, h], &[&r_e, &r_β], n);
    let α_6 = BigUint::commit(&[&c_r_a, g, h], &[&r_e, &r_β, &r_δ], n);
    let α_7 = BigUint::commit(&[g, h], &[&r_ρ_b, &r_ρρ_b], n);

    let c: &BigInt = &challenge(c_e, a, &α_2, &α_3, &α_4, &α_5, &α_6, &α_7).into();

    let s_b = r_b - c * b;
    let s_e = r_e - c * e;
    let s_ρ_b = r_ρ_b - c * &ρ_b;
    let s_r = r_r - c * r;
    let s_r_a = r_r_a - c * &r_a;
    let s_rr_a = r_rr_a - c * &rr_a;
    let s_ρρ_b = r_ρρ_b - c * &ρρ_b;
    let s_β = r_β + c * (e * r_a + ρ_b);
    let s_δ = r_δ + c * (e * rr_a + ρρ_b);

    Proof {
        c_a,
        c_r_a,
        c_b,
        c_ρ_b,
        α_2,
        α_3,
        α_4,
        α_5,
        α_6,
        α_7,
        s_b,
        s_e,
        s_ρ_b,
        s_r,
        s_r_a,
        s_rr_a,
        s_ρρ_b,
        s_β,
        s_δ,
    }
}

pub fn verify<E: Pairing>(pp: &Params<E>, s: &Statement, π: &Proof) -> bool {
    let accumulator::Parameters { g, h, n } = &pp.r;
    let Statement { c_e, a } = s;
    let Proof {
        c_a,
        c_r_a,
        c_b,
        c_ρ_b,
        α_2,
        α_3,
        α_4,
        α_5,
        α_6,
        α_7,
        s_b,
        s_e,
        s_ρ_b,
        s_r,
        s_r_a,
        s_rr_a,
        s_ρρ_b,
        s_β,
        s_δ,
    } = π;

    let c = &challenge(c_e, a, α_2, α_3, α_4, α_5, α_6, α_7).into();

    let res = true;
    res && *α_2 == BigUint::commit(&[c_b, a, h], &[c, s_b, s_ρ_b], n)
        && *α_3 == BigUint::commit(&[c_e, g, h], &[c, s_e, s_r], n)
        && *α_4 == BigUint::commit(&[c_r_a, g, h], &[c, s_r_a, s_rr_a], n)
        && *α_5 == BigUint::commit(&[c_a, g, h, c_b], &[s_e, c, s_β, &-c], n)
        && *α_6 == BigUint::commit(&[c_r_a, g, h, c_ρ_b], &[s_e, s_β, s_δ, &-c], n)
        && *α_7 == BigUint::commit(&[c_ρ_b, g, h], &[c, s_ρ_b, s_ρρ_b], n)
        && s_e.abs() <= BigInt::from(2i8).pow(λ_z + λ_s + μ + 1)
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use num_prime::RandPrime;

    use super::*;
    use crate::utils::ToTransaction;

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let r = &rng.gen_bigint(123);
        let e: BigUint = rng.gen_prime(123, None);
        let other_e_product: BigUint = rng.gen_prime(123, None);
        let e: &BigInt = &e.into();

        let a = &pp.r.g.mod_exp(&other_e_product, &pp.r.n);

        let c_e = &BigUint::commit(&[&pp.r.g, &pp.r.h], &[e, r], &pp.r.n);

        let s = Statement { c_e, a };

        let w = Witness { w: &other_e_product, r, e };

        let π = prove(pp, &s, w);
        assert!(verify(pp, &s, &π));

        println!("{}", pp.r.n.to_tx());
        println!("{}", pp.r.g.to_tx());
        println!("{}", pp.r.h.to_tx());
        println!("{}", λ_z + λ_s + μ + 1);
        println!("{}", λ_s);

        println!(
            "{}",
            vec![
                a.to_tx(),
                c_e.to_tx(),
                π.c_a.to_tx(),
                π.c_r_a.to_tx(),
                π.c_b.to_tx(),
                π.c_ρ_b.to_tx(),
                [π.s_b, π.s_e, π.s_ρ_b, π.s_r, π.s_r_a, π.s_rr_a, π.s_ρρ_b, π.s_β, π.s_δ,].to_tx(),
                [π.α_2, π.α_3, π.α_4, π.α_5, π.α_6, π.α_7,].to_tx(),
            ]
            .join(",")
        );
    }
}
