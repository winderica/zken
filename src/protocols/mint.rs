use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use rand::Rng;
use secp256k1::PublicKey;

use super::{Params, SecretToken, TK};

pub fn mint<E: Pairing, R: Rng>(
    pp: &Params<E>,
    rng: &mut R,
    apk: &PublicKey,
    v: E::ScalarField,
) -> (SecretToken<E::ScalarField>, E::ScalarField) {
    let rho_sn = E::ScalarField::rand(rng);
    let rho_pt = E::ScalarField::rand(rng);
    let (pt, aux_pt) = TK::pt_gen(pp, apk, v, rho_sn, rho_pt);
    let st = SecretToken { v, rho_sn, rho_pt, aux_pt };
    (st, pt)
}
