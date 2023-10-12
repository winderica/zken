use ark_ff::PrimeField;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::SynthesisError;
use ark_std::{marker::PhantomData, vec::Vec};

use super::PoseidonParameters;
use crate::constants::WIDTH;

pub struct CRHGadget<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> CRHGadget<F> {
    pub fn hash(
        pp: &PoseidonParameters<F>,
        a: FpVar<F>,
        b: FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut state = vec![FpVar::Constant(F::from(1u128 << 66)), a, b];
        PoseidonSpongeGadget::permute(pp, &mut state)?;
        Ok(state.pop().unwrap())
    }
}

pub struct EncryptionGadget<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> EncryptionGadget<F> {
    pub fn encrypt(
        pp: &PoseidonParameters<F>,
        m: Vec<FpVar<F>>,
        k: FpVar<F>,
        nonce: FpVar<F>,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let mut state = vec![FpVar::Constant(F::from(1u128 << 32)), k, nonce];
        let mut c = vec![];
        for chunk in m.chunks(WIDTH - 1) {
            PoseidonSpongeGadget::permute(pp, &mut state)?;
            for i in 0..chunk.len() {
                state[i + 1] = &state[i + 1] + &chunk[i];
                c.push(state[i + 1].clone());
            }
        }
        PoseidonSpongeGadget::permute(pp, &mut state)?;
        c.push(state.pop().unwrap());
        Ok(c)
    }
}

#[derive(Clone)]
pub struct PoseidonSpongeGadget<F: PrimeField> {
    field_phantom: PhantomData<F>,
}

impl<F: PrimeField> PoseidonSpongeGadget<F> {
    fn apply_s_box(
        pp: &PoseidonParameters<F>,
        state: &mut [FpVar<F>],
        is_full_round: bool,
    ) -> Result<(), SynthesisError> {
        if is_full_round {
            for state_item in state.iter_mut() {
                *state_item = state_item.pow_by_constant([pp.alpha])?;
            }
        } else {
            state[0] = state[0].pow_by_constant([pp.alpha])?;
        }

        Ok(())
    }

    fn apply_ark(pp: &PoseidonParameters<F>, state: &mut [FpVar<F>], round_number: usize) {
        for (i, state_elem) in state.iter_mut().enumerate() {
            *state_elem += pp.ark[round_number][i];
        }
    }

    fn apply_mds(pp: &PoseidonParameters<F>, state: &mut [FpVar<F>]) {
        let mut new_state = Vec::new();
        let zero = FpVar::<F>::zero();
        for i in 0..state.len() {
            let mut cur = zero.clone();
            for (j, state_elem) in state.iter().enumerate() {
                let term = state_elem * pp.mds[i][j];
                cur += &term;
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()]);
    }

    fn permute(pp: &PoseidonParameters<F>, state: &mut [FpVar<F>]) -> Result<(), SynthesisError> {
        let full_rounds_over_2 = pp.full_rounds / 2;
        for i in 0..full_rounds_over_2 {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, true)?;
            Self::apply_mds(pp, state);
        }
        for i in full_rounds_over_2..(full_rounds_over_2 + pp.partial_rounds) {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, false)?;
            Self::apply_mds(pp, state);
        }
        for i in (full_rounds_over_2 + pp.partial_rounds)..(pp.partial_rounds + pp.full_rounds) {
            Self::apply_ark(pp, state, i);
            Self::apply_s_box(pp, state, true)?;
            Self::apply_mds(pp, state);
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use ark_bn254::Fr;
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;

    use super::*;
    use crate::{
        constants::{ALPHA, R_F, R_P, WIDTH},
        primitives::poseidon::{Encryption, PoseidonParameters, CRH},
    };

    #[test]
    fn test_hash() {
        let rng = &mut ark_std::test_rng();

        let a = Fr::rand(rng);
        let b = Fr::rand(rng);

        let params = PoseidonParameters::gen(R_F, R_P, ALPHA, WIDTH);

        let h = CRH::hash(&params, a, b);

        let cs = ConstraintSystem::new_ref();

        let a_var = FpVar::new_witness(cs.clone(), || Ok(a)).unwrap();
        let b_var = FpVar::new_witness(cs.clone(), || Ok(b)).unwrap();

        let h_var = CRHGadget::hash(&params, a_var, b_var).unwrap();

        assert_eq!(h, h_var.value().unwrap());
    }

    #[test]
    fn test_encrypt() {
        let rng = &mut ark_std::test_rng();

        let mut m = vec![];
        for _ in 0..20 {
            m.push(Fr::rand(rng));
        }
        let k = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let params = PoseidonParameters::gen(R_F, R_P, ALPHA, WIDTH);
        let c = Encryption::encrypt(&params, m.clone(), k, nonce);
        assert_eq!(m, Encryption::decrypt(&params, c.clone(), k, nonce).unwrap());

        let cs = ConstraintSystem::new_ref();

        let m_var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(m)).unwrap();
        let k_var = FpVar::new_witness(cs.clone(), || Ok(k)).unwrap();
        let nonce_var = FpVar::new_witness(cs, || Ok(nonce)).unwrap();

        let c_var = EncryptionGadget::encrypt(&params, m_var, k_var, nonce_var).unwrap();

        assert_eq!(c, c_var.value().unwrap());
    }
}
