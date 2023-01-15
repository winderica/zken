use std::str::FromStr;

use num::bigint::{BigUint, RandBigInt};
use rand::Rng;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Parameters {
    pub g: BigUint,
    pub h: BigUint,
    pub n: BigUint,
}

impl Parameters {
    pub fn new<R: Rng>(rng: &mut R) -> Self {
        let n = BigUint::from_str("25195908475657893494027183240048398571429282126204032027777137836043662020707595556264018525880784406918290641249515082189298559149176184502808489120072844992687392807287776735971418347270261896375014971824691165077613379859095700097330459748808428401797429100642458691817195118746121515172654632282216869987549182422433637259085141865462043576798423387184774447920739934236584823824281198163815010674810451660377306056201619676256133844143603833904414952634432190114657544454178424020924616515723350778707749817125772467962926386356373289912154831438167899885040445364023527381951378636564391212010397122822120720357").unwrap();
        let g = BigUint::from(2u8);
        let h = g.modpow(&rng.gen_biguint_below(&(&n / 2u8)), &n);
        Self { n, g, h }
    }
}

pub struct Accumulator {}

impl Accumulator {
    pub fn acc(pp: &Parameters, w: &BigUint, e: &BigUint) -> BigUint {
        w.modpow(&e, &pp.n)
    }
}

pub struct IntegerCommitment {}

impl IntegerCommitment {
    pub fn commit(pp: &Parameters, e: &BigUint, r: &BigUint) -> BigUint {
        pp.g.modpow(e, &pp.n) * pp.h.modpow(r, &pp.n) % &pp.n
    }
}

#[cfg(test)]
mod tests {
    use rand::thread_rng;

    use super::*;

    #[test]
    fn test_accumulator() {
        let rng = &mut thread_rng();

        let pp = Parameters::new(rng);

        let x = rng.gen_biguint_below(&pp.n);
        let w = rng.gen_biguint_below(&pp.n);

        let acc = Accumulator::acc(&pp, &w, &x);

        assert_eq!(acc, w.modpow(&x, &pp.n));
    }
}
