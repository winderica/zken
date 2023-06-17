use ark_ec::pairing::Pairing;
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    fields::fp::FpVar,
    prelude::{Boolean, FieldVar},
    ToBitsGadget,
};
use ark_relations::r1cs::SynthesisError;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand::{thread_rng, Rng};
use serde::{Deserialize, Serialize};
use serde_with::serde_as;

use crate::{
    lego::{generate_random_parameters_incl_cp_link, LinkPublicGenerators, ProvingKeyWithLink},
    primitives::{
        accumulator,
        poseidon::{
            constraints::{CRHGadget, HPrimeGadget},
            HPrime, PoseidonParameters, CRH,
        },
        secp256k1::constraints::SecretKeyVar,
    },
    proofs::{bind_id, pt_form, range, recv, sn_form, sn_range},
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
    pub r: accumulator::Parameters,
    #[serde_as(as = "_")]
    pub c: LinkPublicGenerators<E>,
}

impl<E: Pairing> Default for Params<E> {
    fn default() -> Self {
        let rng = &mut thread_rng();
        Self {
            h: Default::default(),
            r: accumulator::Parameters::new(rng),
            c: LinkPublicGenerators::new(rng),
        }
    }
}

#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct CRS<E: Pairing> {
    pub pt_form: ProvingKeyWithLink<E>,
    pub sn_form: ProvingKeyWithLink<E>,
    pub sn_range: ProvingKeyWithLink<E>,
    pub recv: ProvingKeyWithLink<E>,
    pub range: ProvingKeyWithLink<E>,
    pub bind_id: ProvingKeyWithLink<E>,
}

impl<E: Pairing> CRS<E> {
    pub fn setup<R: Rng>(pp: &Params<E>, rng: &mut R) -> Result<Self, SynthesisError> {
        Ok(Self {
            pt_form: generate_random_parameters_incl_cp_link(
                pt_form::Circuit { pp, w: Default::default() },
                &pp.c,
                3,
                rng,
            )?,
            sn_form: generate_random_parameters_incl_cp_link(
                sn_form::Circuit { pp, w: Default::default() },
                &pp.c,
                3,
                rng,
            )?,
            sn_range: generate_random_parameters_incl_cp_link(
                sn_range::Circuit { pp, w: Default::default() },
                &pp.c,
                2,
                rng,
            )?,
            recv: generate_random_parameters_incl_cp_link(
                recv::Circuit { pp, s: Default::default(), w: Default::default() },
                &pp.c,
                1,
                rng,
            )?,
            range: generate_random_parameters_incl_cp_link(
                range::Circuit { pp, s: Default::default(), w: Default::default() },
                &pp.c,
                1,
                rng,
            )?,
            bind_id: generate_random_parameters_incl_cp_link(
                bind_id::Circuit { pp, s: Default::default(), w: Default::default() },
                &pp.c,
                1,
                rng,
            )?,
        })
    }
}

pub struct SecretToken<F: PrimeField> {
    pub v: F,
    pub rho_pt: F,
    pub aux_pt: Vec<Vec<bool>>,
}

pub struct TK {}
impl TK {
    pub fn pt_gen<E: Pairing>(
        pp: &Params<E>,
        h_apk: E::ScalarField,
        v: E::ScalarField,
        rho_pt: E::ScalarField,
    ) -> (E::ScalarField, Vec<Vec<bool>>) {
        HPrime::find_hash(&pp.h, h_apk, v, rho_pt, Default::default())
    }
}

pub struct TokenGadget {}

impl TokenGadget {
    pub fn pt_gen<E: Pairing, const W: usize>(
        pp: &Params<E>,
        h_apk: FpVar<E::ScalarField>,
        v: FpVar<E::ScalarField>,
        rho_pt: FpVar<E::ScalarField>,
        aux_pt: &[Vec<Boolean<E::ScalarField>>],
    ) -> Result<FpVar<E::ScalarField>, SynthesisError> {
        HPrimeGadget::hash::<E::ScalarField, W>(&pp.h, h_apk, v, rho_pt, FpVar::zero(), aux_pt)
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
            F::from_le_bytes_mod_order(sk0),
            F::from_le_bytes_mod_order(sk1),
            pt,
            Default::default(),
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
            Boolean::le_bits_to_fp_var(sk0)?,
            Boolean::le_bits_to_fp_var(sk1)?,
            pt,
            FpVar::zero(),
        )?;
        let h_bits = h.to_bits_le()?;
        Boolean::le_bits_to_fp_var(&h_bits[1..])
    }
}

pub struct SNRange {}

impl SNRange {
    pub fn h_range_gen<E: Pairing, F: PrimeField>(
        pp: &Params<E>,
        range: (F, F),
    ) -> (F, Vec<Vec<bool>>)
    where
        E: Pairing<ScalarField = F>,
    {
        HPrime::find_hash(&pp.h, range.0, range.1, Default::default(), Default::default())
    }
}

pub struct SNRangeGadget {}

impl SNRangeGadget {
    pub fn h_range_gen<E: Pairing, F: PrimeField, const W: usize>(
        pp: &Params<E>,
        range: (FpVar<F>, FpVar<F>),
        aux_range: &[Vec<Boolean<F>>],
    ) -> Result<FpVar<F>, SynthesisError>
    where
        E: Pairing<ScalarField = F>,
    {
        HPrimeGadget::hash::<F, W>(&pp.h, range.0, range.1, FpVar::zero(), FpVar::zero(), aux_range)
    }
}
