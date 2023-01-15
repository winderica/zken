use ark_ec::pairing::Pairing;
use ark_ff::{BigInteger, BitIteratorLE, PrimeField};
use ark_r1cs_std::{
    fields::fp::FpVar,
    prelude::{Boolean, FieldVar},
    ToBitsGadget
};
use ark_relations::r1cs::SynthesisError;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use num::{BigUint, Integer};
use rand::{thread_rng, Rng};
use secp256k1::PublicKey;
use serde::{Deserialize, Serialize};
use serde_with::serde_as;

use crate::{
    lego::{generate_random_parameters_incl_cp_link, LinkPublicGenerators, ProvingKeyWithLink},
    primitives::{
        accumulator,
        poseidon::{constraints::{HPrimeGadget, CRHGadget}, HPrime, PoseidonParameters, CRH},
        secp256k1::{constraints::PointVar, SecretKey},
    },
    proofs::{bind_id, pt_form, sn_form, range, recv, sn_range},
    utils::ToVecF,
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
                5,
                rng,
            )?,
            sn_form: generate_random_parameters_incl_cp_link(
                sn_form::Circuit { pp, w: Default::default() },
                &pp.c,
                4,
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
                2,
                rng,
            )?,
        })
    }
}

pub struct SecretToken<F: PrimeField> {
    pub v: F,
    pub rho_sn: F,
    pub rho_pt: F,
    pub aux_pt: Vec<Vec<bool>>,
}

pub struct TK {}
impl TK {
    pub fn pt_gen<E: Pairing>(
        pp: &Params<E>,
        apk: &PublicKey,
        v: E::ScalarField,
        rho_sn: E::ScalarField,
        rho_pt: E::ScalarField,
    ) -> (E::ScalarField, Vec<Vec<bool>>) {
        HPrime::find_hash(&pp.h, CRH::hash_vec(&pp.h, &apk.to_vec_f(128)), v, rho_sn, rho_pt)
    }
}

pub struct TokenGadget {}

impl TokenGadget {
    pub fn pt_gen<E: Pairing, const W: usize>(
        pp: &Params<E>,
        apk: &PointVar<E::ScalarField, W>,
        v: FpVar<E::ScalarField>,
        rho_sn: FpVar<E::ScalarField>,
        rho_pt: FpVar<E::ScalarField>,
        aux_pt: &[Vec<Boolean<E::ScalarField>>],
    ) -> Result<FpVar<E::ScalarField>, SynthesisError> {
        HPrimeGadget::hash::<E::ScalarField, W>(&pp.h, apk.hash(&pp.h)?, v, rho_sn, rho_pt, aux_pt)
    }
}

impl<F: PrimeField> ToVecF<F> for BigUint {
    fn to_vec_f(&self, width: usize) -> Vec<F> {
        assert!(width.is_multiple_of(&8));
        BitIteratorLE::new(self.to_u64_digits())
            .collect::<Vec<_>>()
            .chunks(width)
            .map(F::BigInt::from_bits_le)
            .map(F::from_bigint)
            .collect::<Option<_>>()
            .unwrap()
    }
}

impl<F: PrimeField> ToVecF<F> for [u8] {
    fn to_vec_f(&self, width: usize) -> Vec<F> {
        assert!(width.is_multiple_of(&8));
        self.chunks(width / 8).map(F::from_le_bytes_mod_order).collect()
    }
}

impl<F: PrimeField> ToVecF<F> for SecretKey {
    fn to_vec_f(&self, width: usize) -> Vec<F> {
        assert!(width.is_multiple_of(&8));
        self.secret_bytes().rchunks(width / 8).map(F::from_be_bytes_mod_order).collect()
    }
}

impl<F: PrimeField> ToVecF<F> for PublicKey {
    fn to_vec_f(&self, width: usize) -> Vec<F> {
        assert!(width.is_multiple_of(&8));
        let bits = self.serialize_uncompressed();
        let x_bits = &bits[1..33];
        let y_bits = &bits[33..65];
        [
            x_bits.rchunks(width / 8).map(F::from_be_bytes_mod_order).collect::<Vec<_>>(),
            y_bits.rchunks(width / 8).map(F::from_be_bytes_mod_order).collect(),
        ]
        .concat()
    }
}

pub struct SN {}
impl SN {
    pub fn sn_gen<E: Pairing, F: PrimeField>(
        pp: &Params<E>,
        ask: &SecretKey,
        rho_sn: F,
    ) -> F where E: Pairing<ScalarField = F> {
        let sk_chunks = ask.to_vec_f(128);
        let h = CRH::hash(&pp.h, sk_chunks[0], sk_chunks[1], rho_sn, Default::default());
        let h_bits = h.into_bigint().to_bits_le();
        F::from_bigint(F::BigInt::from_bits_le(&h_bits[1..])).unwrap()
    }
}

pub struct SNGadget {}

impl SNGadget {
    pub fn sn_gen<E: Pairing, F: PrimeField>(
        pp: &Params<E>,
        sk: (FpVar<F>, FpVar<F>),
        rho_sn: FpVar<F>,
    ) -> Result<FpVar<F>, SynthesisError> where E: Pairing<ScalarField = F> {
        let h = CRHGadget::hash(&pp.h, sk.0, sk.1, rho_sn, FpVar::zero())?;
        let h_bits = h.to_bits_le()?;
        Boolean::le_bits_to_fp_var(&h_bits[1..])
    }
}

pub struct SNRange {}

impl SNRange {
    pub fn h_range_gen<E: Pairing, F: PrimeField>(
        pp: &Params<E>,
        range: (F, F),
    ) -> (F, Vec<Vec<bool>>) where E: Pairing<ScalarField = F> {
        HPrime::find_hash(&pp.h, range.0, range.1, Default::default(), Default::default())
    }
}

pub struct SNRangeGadget {}

impl SNRangeGadget {
    pub fn h_range_gen<E: Pairing, F: PrimeField, const W: usize>(
        pp: &Params<E>,
        range: (FpVar<F>, FpVar<F>),
        aux_range: &[Vec<Boolean<F>>],
    ) -> Result<FpVar<F>, SynthesisError> where E: Pairing<ScalarField = F> {
        HPrimeGadget::hash::<F, W>(&pp.h, range.0, range.1, FpVar::zero(), FpVar::zero(), aux_range)
    }
}