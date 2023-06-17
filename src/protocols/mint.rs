use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use rand::Rng;

use super::{Params, SecretToken, TK};
use crate::primitives::poseidon::HField;

pub fn mint<E: Pairing, R: Rng>(
    pp: &Params<E>,
    rng: &mut R,
    apk: &ark_secp256k1::Affine,
    v: E::ScalarField,
) -> (SecretToken<E::ScalarField>, E::ScalarField) {
    let rho_pt = E::ScalarField::rand(rng);
    let (pt, aux_pt) = TK::pt_gen(pp, apk.hash_to_field(&pp.h), v, rho_pt);
    let st = SecretToken { v, rho_pt, aux_pt };
    (st, pt)
}
