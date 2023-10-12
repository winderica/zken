use ark_ec::pairing::Pairing;
use ark_ff::{PrimeField, BigInteger};
use ark_r1cs_std::{
    alloc::AllocVar, eq::EqGadget, fields::fp::FpVar, ToBitsGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use serde::{Deserialize, Serialize};
use serde_with::serde_as;

use crate::{
    constants::W,
    primitives::{
        poseidon::{constraints::CRHGadget, HFieldGadget},
        secp256k1::constraints::{PointVar, Secp256k1Gadget, SecretKeyVar},
    },
    proofs::Circuit,
    protocols::Params,
    utils::num_constraints,
};
#[serde_as]
#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Statement {
    #[serde_as(as = "crate::utils::SerdeAs")]
    pub wpk: ark_secp256k1::Affine,
}

#[derive(Clone, Default)]
pub struct Witness<F: PrimeField> {
    pub h_apk: F,
    pub delta: ark_secp256k1::Fr,
    pub wsk: ark_secp256k1::Fr,
}

pub struct BindIdCircuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub s: Statement,
    pub w: Witness<E::ScalarField>,
}

impl<'a, E: Pairing> Circuit<'a, E> for BindIdCircuit<'a, E> {
    const NUM_COMMIT_WITNESSES: usize = 1;
    const NAME: &'static str = "BindId";
    type Statement = Statement;
    type Witness = Witness<E::ScalarField>;

    fn new(pp: &'a Params<E>, s: Self::Statement, w: Self::Witness) -> Self {
        Self { pp, s, w }
    }

    fn inputize(s: &Self::Statement) -> Vec<E::ScalarField> {
        PointVar::<E::ScalarField, W>::inputize(&s.wpk)
    }
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for BindIdCircuit<'a, E> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<E::ScalarField>,
    ) -> ark_relations::r1cs::Result<()> {
        let Self { s, w, pp } = self;
        let Statement { wpk } = s;
        let Witness { h_apk, delta, wsk } = w;

        let h_apk = FpVar::<E::ScalarField>::new_witness(cs.clone(), || Ok(h_apk))?;
        let delta = FpVar::<E::ScalarField>::new_witness(cs.clone(), || Ok(E::ScalarField::from_le_bytes_mod_order(&delta.into_bigint().to_bytes_le())))?;
        let wsk = FpVar::<E::ScalarField>::new_witness(cs.clone(), || Ok(E::ScalarField::from_le_bytes_mod_order(&wsk.into_bigint().to_bytes_le())))?;

        let wpk = PointVar::<E::ScalarField, W>::new_input(cs.clone(), || Ok(wpk))?;

        println!("Shape check: {}", cs.num_constraints());

        println!(
            "PK derivation: {}",
            num_constraints(&cs, || {
                let sk = CRHGadget::hash(
                    &pp.h,
                    wsk,
                    delta,
                )?.to_bits_le()?;
                wpk.add(&Secp256k1Gadget::pk_gen(&SecretKeyVar(sk))?)?
                    .hash_to_field_var(&pp.h)?
                    .enforce_equal(&h_apk)
            })?
        );

        println!("Total: {}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInteger, UniformRand};
    use ark_serialize::CanonicalSerialize;
    use rand::thread_rng;

    use super::*;
    use crate::{
        primitives::poseidon::{HField, CRH},
        proofs::ProofSystem,
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let wsk = ark_secp256k1::Fr::rand(rng);
        let wpk = (ark_secp256k1::Affine::generator() * wsk).into_affine();
        let delta = ark_secp256k1::Fr::rand(rng);
        let ask = ark_secp256k1::Fr::from_le_bytes_mod_order(
            &CRH::hash(
                &pp.h,
                Fr::from_le_bytes_mod_order(&wsk.into_bigint().to_bytes_le()),
                Fr::from_le_bytes_mod_order(&delta.into_bigint().to_bytes_le()),
            )
            .into_bigint()
            .to_bytes_le(),
        ) + wsk;
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_h_apk = Fr::rand(rng);

        let s = Statement { wpk };
        let w = Witness { h_apk, delta, wsk };

        let link_v = [r_h_apk];

        let crs = ProofSystem::<_, BindIdCircuit<_>>::setup(&pp, rng).unwrap();

        println!("{}", crs.pk.compressed_size());

        let proof_link = crs.prove(s.clone(), w, &link_v, rng).unwrap();

        println!("{}", proof_link.compressed_size());

        assert!(crs.verify(&s, &proof_link).unwrap());

        crs.print_on_chain(&s, &proof_link);
    }

    #[bench]
    fn bench_keygen(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        b.iter(|| ProofSystem::<_, BindIdCircuit<_>>::setup(&pp, rng).unwrap());
    }

    #[bench]
    fn bench_prove(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let wsk = ark_secp256k1::Fr::rand(rng);
        let wpk = (ark_secp256k1::Affine::generator() * wsk).into_affine();
        let delta = ark_secp256k1::Fr::rand(rng);
        let ask = ark_secp256k1::Fr::from_le_bytes_mod_order(
            &CRH::hash(
                &pp.h,
                Fr::from_le_bytes_mod_order(&wsk.into_bigint().to_bytes_le()),
                Fr::from_le_bytes_mod_order(&delta.into_bigint().to_bytes_le()),
            )
            .into_bigint()
            .to_bytes_le(),
        ) + wsk;
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_h_apk = Fr::rand(rng);

        let s = Statement { wpk };
        let w = Witness { h_apk, delta, wsk };

        let link_v = [r_h_apk];

        let crs = ProofSystem::<_, BindIdCircuit<_>>::setup(&pp, rng).unwrap();

        b.iter(|| crs.prove(s.clone(), w.clone(), &link_v, rng).unwrap());
    }

    #[bench]
    fn bench_verify(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let wsk = ark_secp256k1::Fr::rand(rng);
        let wpk = (ark_secp256k1::Affine::generator() * wsk).into_affine();
        let delta = ark_secp256k1::Fr::rand(rng);
        let ask = ark_secp256k1::Fr::from_le_bytes_mod_order(
            &CRH::hash(
                &pp.h,
                Fr::from_le_bytes_mod_order(&wsk.into_bigint().to_bytes_le()),
                Fr::from_le_bytes_mod_order(&delta.into_bigint().to_bytes_le()),
            )
            .into_bigint()
            .to_bytes_le(),
        ) + wsk;
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_h_apk = Fr::rand(rng);

        let s = Statement { wpk };
        let w = Witness { h_apk, delta, wsk };

        let link_v = [r_h_apk];

        let crs = ProofSystem::<_, BindIdCircuit<_>>::setup(&pp, rng).unwrap();

        let proof_link = crs.prove(s.clone(), w, &link_v, rng).unwrap();

        b.iter(|| crs.verify(&s, &proof_link).unwrap())
    }
}
