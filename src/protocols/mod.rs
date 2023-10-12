use ark_ec::pairing::Pairing;
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{fields::fp::FpVar, prelude::Boolean, ToBitsGadget};
use ark_relations::r1cs::SynthesisError;
use rand::{thread_rng, Rng};
use serde::{Deserialize, Serialize};
use serde_with::serde_as;

use crate::{
    lego::LinkPublicGenerators,
    primitives::{
        poseidon::{constraints::CRHGadget, PoseidonParameters, CRH},
        secp256k1::constraints::SecretKeyVar,
    },
    proofs::{
        bind_id::BindIdCircuit, pt_form::PTCircuit, recv::RecvCircuit, sn_form::SNCircuit,
        ProofSystem,
    },
};

pub mod mint;
pub mod pour;
pub mod reveal;

#[serde_as]
#[derive(Clone, Serialize, Deserialize)]
pub struct Params<E: Pairing> {
    #[serde_as(as = "_")]
    pub h: PoseidonParameters<E::ScalarField>,
    #[serde_as(as = "_")]
    pub c: LinkPublicGenerators<E>,
}

impl<E: Pairing> Default for Params<E> {
    fn default() -> Self {
        let rng = &mut thread_rng();
        Self { h: Default::default(), c: LinkPublicGenerators::new(rng) }
    }
}

pub struct GlobalCRS<'a, E: Pairing> {
    pub pt_form: ProofSystem<'a, E, PTCircuit<'a, E>>,
    pub sn_form: ProofSystem<'a, E, SNCircuit<'a, E>>,
    pub recv: ProofSystem<'a, E, RecvCircuit<'a, E>>,
    pub bind_id: ProofSystem<'a, E, BindIdCircuit<'a, E>>,
}

impl<'a, E: Pairing> GlobalCRS<'a, E> {
    pub fn setup<R: Rng>(pp: &'a Params<E>, rng: &mut R) -> Result<Self, SynthesisError> {
        Ok(Self {
            pt_form: ProofSystem::setup(&pp, rng)?,
            sn_form: ProofSystem::setup(&pp, rng)?,
            recv: ProofSystem::setup(&pp, rng)?,
            bind_id: ProofSystem::setup(&pp, rng)?,
        })
    }
}

#[derive(Clone, Copy)]
pub struct SecretToken<F: PrimeField> {
    pub v: F,
    pub rho: F,
}

pub struct TK {}
impl TK {
    pub fn pt_gen<E: Pairing>(
        pp: &Params<E>,
        h_apk: E::ScalarField,
        v: E::ScalarField,
        rho: E::ScalarField,
    ) -> E::ScalarField {
        CRH::hash(&pp.h, CRH::hash(&pp.h, h_apk, v), rho)
    }
}

pub struct TokenGadget {}

impl TokenGadget {
    pub fn pt_gen<E: Pairing, const W: usize>(
        pp: &Params<E>,
        h_apk: FpVar<E::ScalarField>,
        v: FpVar<E::ScalarField>,
        rho: FpVar<E::ScalarField>,
    ) -> Result<FpVar<E::ScalarField>, SynthesisError> {
        CRHGadget::hash(&pp.h, CRHGadget::hash(&pp.h, h_apk, v)?, rho)
    }
}

pub struct SN {}
impl SN {
    pub fn sn_gen<E: Pairing, F: PrimeField>(pp: &Params<E>, ask: &ark_secp256k1::Fr, pt: F) -> F
    where
        E: Pairing<ScalarField = F>,
    {
        let sk_bits = ask.into_bigint().to_bytes_le();
        let (sk0, sk1) = sk_bits.split_at(16);

        let h = CRH::hash(
            &pp.h,
            CRH::hash(&pp.h, F::from_le_bytes_mod_order(sk0), F::from_le_bytes_mod_order(sk1)),
            pt,
        );
        let h_bits = h.into_bigint().to_bits_le();
        F::from_bigint(F::BigInt::from_bits_le(&h_bits[1..])).unwrap()
    }
}

pub struct SNGadget {}

impl SNGadget {
    pub fn sn_gen<E: Pairing, F: PrimeField>(
        pp: &Params<E>,
        sk: SecretKeyVar<F>,
        pt: FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError>
    where
        E: Pairing<ScalarField = F>,
    {
        let (sk0, sk1) = sk.0.split_at(128);
        let h = CRHGadget::hash(
            &pp.h,
            CRHGadget::hash(
                &pp.h,
                Boolean::le_bits_to_fp_var(sk0)?,
                Boolean::le_bits_to_fp_var(sk1)?,
            )?,
            pt,
        )?;
        let h_bits = h.to_bits_le()?;
        Boolean::le_bits_to_fp_var(&h_bits[1..])
    }
}
