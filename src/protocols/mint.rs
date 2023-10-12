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
    let pt = TK::pt_gen(pp, apk.hash_to_field(&pp.h), v, rho_pt);
    let st = SecretToken { v, rho: rho_pt };
    (st, pt)
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ec::{AffineRepr, CurveGroup};
    use rand::thread_rng;

    use super::*;

    #[bench]
    fn bench_mint(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let ask = ark_secp256k1::Fr::rand(rng);
        let apk = (ark_secp256k1::Affine::generator() * ask).into_affine();

        let v = Fr::rand(rng);

        b.iter(|| mint(pp, rng, &apk, v));
    }
}
