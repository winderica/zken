use std::marker::PhantomData;

use ark_ec::pairing::Pairing;
use ark_relations::r1cs::{ConstraintSynthesizer, SynthesisError};
use ark_std::UniformRand;
use rand::Rng;

use crate::{
    lego::{
        create_random_proof_incl_cp_link, generate_random_parameters_incl_cp_link,
        prepare_verifying_key, verify_proof_incl_cp_link, PreparedVerifyingKey, ProofWithLink,
        ProvingKeyWithLink, VerifyingKeyWithLink,
    },
    protocols::Params,
    utils::{OnChainVerifiable, ToSolidity, ToTransaction},
};

pub mod bind_id;
pub mod custom;
pub mod pt_form;
pub mod recv;
pub mod sn_form;

pub trait Circuit<'a, E: Pairing>: ConstraintSynthesizer<E::ScalarField> {
    const NUM_COMMIT_WITNESSES: usize;
    const NAME: &'static str;
    type Statement: Default;
    type Witness: Default;

    fn new(pp: &'a Params<E>, s: Self::Statement, w: Self::Witness) -> Self;

    fn inputize(s: &Self::Statement) -> Vec<E::ScalarField>;
}

pub struct ProofSystem<'a, E: Pairing, C: Circuit<'a, E>> {
    _c: PhantomData<C>,
    pub pp: &'a Params<E>,
    pub pk: ProvingKeyWithLink<E>,
    pub vk: VerifyingKeyWithLink<E>,
    pub pvk: PreparedVerifyingKey<E>,
}

impl<'a, E: Pairing, C: Circuit<'a, E>> ProofSystem<'a, E, C> {
    pub fn setup<R: Rng>(pp: &'a Params<E>, rng: &mut R) -> Result<Self, SynthesisError> {
        let pk = generate_random_parameters_incl_cp_link(
            C::new(pp, C::Statement::default(), C::Witness::default()),
            &pp.c,
            C::NUM_COMMIT_WITNESSES,
            rng,
        )?;
        let vk = pk.vk.clone();
        let pvk = prepare_verifying_key(&vk.groth16_vk);
        Ok(ProofSystem { _c: Default::default(), pp, pk, vk, pvk })
    }

    pub fn prove<R: Rng>(
        &self,
        s: C::Statement,
        w: C::Witness,
        openings: &[E::ScalarField],
        rng: &mut R,
    ) -> Result<ProofWithLink<E>, SynthesisError> {
        create_random_proof_incl_cp_link(
            C::new(self.pp, s, w),
            E::ScalarField::rand(rng),
            openings,
            &self.pk,
            rng,
        )
    }

    pub fn verify(&self, s: &C::Statement, pi: &ProofWithLink<E>) -> Result<bool, SynthesisError> {
        verify_proof_incl_cp_link(&self.pvk, &self.vk, pi, &C::inputize(s))
    }

    pub fn print_on_chain(&self, s: &C::Statement, pi: &ProofWithLink<E>)
    where
        E::G1Affine: ToSolidity + ToTransaction,
        E::G2Affine: ToSolidity + ToTransaction,
        E::ScalarField: ToTransaction,
    {
        println!("{}", self.vk.to_on_chain_verifier(C::NAME));
        println!(
            "{}",
            vec![
                pi.groth16_proof.a.to_tx(),
                pi.groth16_proof.b.to_tx(),
                pi.groth16_proof.c.to_tx(),
                vec![pi.link_d.clone(), vec![pi.groth16_proof.d], vec![pi.link_pi]]
                    .concat()
                    .to_tx(),
                C::inputize(s).to_tx(),
            ]
            .join(",")
        );
    }
}
