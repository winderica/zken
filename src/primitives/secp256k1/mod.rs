use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};

use super::poseidon::{HField, PoseidonParameters, CRH};

pub mod constraints;

impl<F: PrimeField> HField<F> for ark_secp256k1::Affine {
    fn hash_to_field(&self, pp: &PoseidonParameters<F>) -> F {
        let (&x, &y) = self.xy().unwrap();

        CRH::hash_vec(
            pp,
            &x.into_bigint()
                .to_bytes_le()
                .chunks(16)
                .chain(y.into_bigint().to_bytes_le().chunks(16))
                .map(F::from_le_bytes_mod_order)
                .collect::<Vec<_>>(),
        )
    }
}

impl<F: PrimeField> HField<F> for ark_secp256k1::Projective {
    fn hash_to_field(&self, pp: &PoseidonParameters<F>) -> F {
        self.into_affine().hash_to_field(pp)
    }
}
