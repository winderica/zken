use std::collections::HashSet;

use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::SynthesisError;
use ark_std::{marker::PhantomData, vec::Vec};
use num::{BigUint, Zero};
use serde::{Deserialize, Serialize};
use serde_with::serde_as;

use crate::constants::{ALPHA, R_F, R_P, WIDTH};

pub mod constraints;

pub trait HField<F: PrimeField> {
    fn hash_to_field(&self, pp: &PoseidonParameters<F>) -> F;
}

pub trait HFieldGadget<F: PrimeField> {
    fn hash_to_field_var(&self, pp: &PoseidonParameters<F>) -> Result<FpVar<F>, SynthesisError>;
}

#[serde_as]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PoseidonParameters<F: PrimeField> {
    #[serde_as(as = "_")]
    full_rounds: usize,
    #[serde_as(as = "_")]
    partial_rounds: usize,
    #[serde_as(as = "_")]
    alpha: u64,
    #[serde_as(as = "crate::utils::SerdeAs")]
    mds: Vec<Vec<F>>,
    #[serde_as(as = "crate::utils::SerdeAs")]
    ark: Vec<Vec<F>>,
}

impl<F: PrimeField> Default for PoseidonParameters<F> {
    fn default() -> Self {
        Self::gen(R_F, R_P, ALPHA, WIDTH)
    }
}

impl<F: PrimeField> PoseidonParameters<F> {
    pub fn gen(r_f: usize, r_p: usize, alpha: u64, width: usize) -> Self {
        const FIELD_TYPE: u16 = 1;
        const S_BOX_TYPE: u32 = 0;
        let m: BigUint = F::MODULUS.into();
        let m_bits = F::MODULUS_BIT_SIZE;

        let mut bits = format!(
            "{FIELD_TYPE:02b}{S_BOX_TYPE:04b}{m_bits:012b}{width:012b}{r_f:010b}{r_p:010b}{}",
            "1".repeat(30)
        )
        .chars()
        .map(|i| i == '1')
        .collect::<Vec<_>>();

        let mut round = || -> bool {
            let b = bits[62] ^ bits[51] ^ bits[38] ^ bits[23] ^ bits[13] ^ bits[0];
            bits.remove(0);
            bits.push(b);
            b
        };

        for _ in 0..160 {
            round();
        }

        let mut rng = || -> BigUint {
            (0..m_bits).rev().fold(BigUint::zero(), |mut v, i| loop {
                if round() {
                    v.set_bit(i.into(), round());
                    break v;
                }
                round();
            })
        };

        let round_constants = (0..r_f + r_p)
            .map(|_| {
                (0..width)
                    .map(|_| loop {
                        let r = rng();
                        if r < m {
                            return F::from(r);
                        }
                    })
                    .collect()
            })
            .collect();

        let mds_matrix = loop {
            let v = (0..width * 2).map(|_| F::from(rng())).collect::<Vec<_>>();

            if HashSet::<F>::from_iter(v.clone()).len() == width * 2 {
                let (x, y) = v.split_at(width);
                break x
                    .iter()
                    .map(|i| y.iter().map(|j| i.add(j).inverse()).collect())
                    .collect::<Option<_>>()
                    .unwrap();
            }
        };
        Self { full_rounds: r_f, partial_rounds: r_p, alpha, mds: mds_matrix, ark: round_constants }
    }
}

#[derive(Clone)]
pub struct PoseidonSponge<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> PoseidonSponge<F> {
    fn apply_s_box(pp: &PoseidonParameters<F>, state: &mut [F], is_full_round: bool) {
        if is_full_round {
            for elem in state {
                *elem = elem.pow([pp.alpha]);
            }
        } else {
            state[0] = state[0].pow([pp.alpha]);
        }
    }

    fn apply_ark(pp: &PoseidonParameters<F>, state: &mut [F], round_number: usize) {
        for (i, state_elem) in state.iter_mut().enumerate() {
            state_elem.add_assign(&pp.ark[round_number][i]);
        }
    }

    fn apply_mds(pp: &PoseidonParameters<F>, state: &mut [F]) {
        let mut new_state = Vec::new();
        for i in 0..state.len() {
            let mut cur = F::zero();
            for (j, state_elem) in state.iter().enumerate() {
                let term = state_elem.mul(&pp.mds[i][j]);
                cur.add_assign(&term);
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()])
    }

    fn permute(pp: &PoseidonParameters<F>, state: &mut [F]) {
        let full_rounds_over_2 = pp.full_rounds / 2;
        for i in 0..full_rounds_over_2 {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, true);
            Self::apply_mds(pp, state);
        }
        for i in full_rounds_over_2..(full_rounds_over_2 + pp.partial_rounds) {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, false);
            Self::apply_mds(pp, state);
        }
        for i in (full_rounds_over_2 + pp.partial_rounds)..(pp.partial_rounds + pp.full_rounds) {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, true);
            Self::apply_mds(pp, state);
        }
    }
}

pub struct CRH<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> CRH<F> {
    pub fn hash(pp: &PoseidonParameters<F>, a: F, b: F) -> F {
        let mut state = [F::from(1u128 << 66), a, b];
        PoseidonSponge::permute(pp, &mut state);
        state[WIDTH - 1]
    }

    pub fn hash_vec(pp: &PoseidonParameters<F>, v: &[F]) -> F {
        assert_eq!(v.len(), WIDTH - 1);
        let mut state = vec![F::from(1u128 << 66)];
        state.extend_from_slice(v);
        PoseidonSponge::permute(pp, &mut state);
        state[WIDTH - 1]
    }
}

pub struct Encryption<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> Encryption<F> {
    pub fn encrypt(pp: &PoseidonParameters<F>, m: Vec<F>, k: F, nonce: F) -> Vec<F> {
        let mut state = vec![F::from(1u64 << 32), k, nonce];
        let mut c = vec![];
        for chunk in m.chunks(WIDTH - 1) {
            PoseidonSponge::permute(pp, &mut state);
            for i in 0..chunk.len() {
                state[i + 1] += chunk[i];
                c.push(state[i + 1]);
            }
        }
        PoseidonSponge::permute(pp, &mut state);
        c.push(state.pop().unwrap());
        c
    }

    pub fn decrypt(pp: &PoseidonParameters<F>, mut c: Vec<F>, k: F, nonce: F) -> Option<Vec<F>> {
        let mut state = vec![F::from(1u64 << 32), k, nonce];
        let mut m = vec![];
        let tag = c.pop().unwrap();
        for chunk in c.chunks(WIDTH - 1) {
            PoseidonSponge::permute(pp, &mut state);
            for i in 0..chunk.len() {
                m.push(chunk[i] - state[i + 1]);
                state[i + 1] = chunk[i];
            }
        }
        PoseidonSponge::permute(pp, &mut state);
        if state.pop().unwrap() != tag {
            return None;
        }
        Some(m)
    }
}
