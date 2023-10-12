use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::EqGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use serde::{Deserialize, Serialize};
use serde_with::serde_as;

use crate::{
    constants::W,
    primitives::{
        poseidon::{constraints::EncryptionGadget, HFieldGadget},
        secp256k1::constraints::{PointVar, Secp256k1Gadget, SecretKeyVar},
    },
    proofs::Circuit,
    protocols::{Params, TokenGadget},
    utils::num_constraints,
};

#[serde_as]
#[derive(Clone, Serialize, Deserialize)]
pub struct Statement<F: PrimeField> {
    pub pt_r: F,
    pub extra: Vec<F>,
    #[serde_as(as = "crate::utils::SerdeAs")]
    pub epk_s: ark_secp256k1::Affine,
    pub nonce: F,
}

impl<F: PrimeField> Default for Statement<F> {
    fn default() -> Self {
        Self {
            pt_r: Default::default(),
            extra: vec![F::zero(); 3],
            epk_s: Default::default(),
            nonce: Default::default(),
        }
    }
}

#[derive(Default, Clone)]
pub struct Witness<F: PrimeField> {
    pub v: F,
    pub apk_r: ark_secp256k1::Affine,
    pub rho_pt_r: F,
    pub esk_s: ark_secp256k1::Fr,
}

pub struct RecvCircuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub s: Statement<E::ScalarField>,
    pub w: Witness<E::ScalarField>,
}

impl<'a, E: Pairing> Circuit<'a, E> for RecvCircuit<'a, E> {
    const NUM_COMMIT_WITNESSES: usize = 1;
    const NAME: &'static str = "Recv";
    type Statement = Statement<E::ScalarField>;
    type Witness = Witness<E::ScalarField>;

    fn new(pp: &'a Params<E>, s: Self::Statement, w: Self::Witness) -> Self {
        Self { pp, s, w }
    }

    fn inputize(s: &Self::Statement) -> Vec<E::ScalarField> {
        let mut input = vec![s.pt_r];
        input.extend_from_slice(&s.extra);
        input.extend(PointVar::<E::ScalarField, W>::inputize(&s.epk_s));
        input.push(s.nonce);
        input
    }
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for RecvCircuit<'a, E> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<E::ScalarField>,
    ) -> Result<(), SynthesisError> {
        let Self { pp, s, w } = self;
        let Statement { pt_r, extra, epk_s, nonce } = s;
        let Witness { v, apk_r, rho_pt_r, esk_s } = w;

        let v = FpVar::new_witness(cs.clone(), || Ok(v))?;
        let pt_r = FpVar::new_input(cs.clone(), || Ok(pt_r))?;
        let extra = Vec::new_input(cs.clone(), || Ok(extra))?;
        let epk_s = PointVar::<_, W>::new_input(cs.clone(), || Ok(epk_s))?;
        let nonce = FpVar::new_input(cs.clone(), || Ok(nonce))?;

        let apk_r = PointVar::<_, W>::new_witness(cs.clone(), || Ok(apk_r))?;
        let rho_pt_r = FpVar::new_witness(cs.clone(), || Ok(rho_pt_r))?;
        let esk_s = SecretKeyVar::new_witness(cs.clone(), || Ok(esk_s))?;

        println!("Shape check: {}", cs.num_constraints());

        println!(
            "PT generation: {}",
            num_constraints(&cs, || {
                pt_r.enforce_equal(&TokenGadget::pt_gen::<_, W>(
                    pp,
                    apk_r.hash_to_field_var(&pp.h)?,
                    v.clone(),
                    rho_pt_r.clone(),
                )?)
            })?
        );
        println!(
            "ST encryption: {}",
            num_constraints(&cs, || {
                epk_s.enforce_equal(&Secp256k1Gadget::pk_gen(&esk_s)?)?;
                extra.enforce_equal(&EncryptionGadget::encrypt(
                    &pp.h,
                    vec![v, rho_pt_r],
                    Secp256k1Gadget::key_exchange(&esk_s, &apk_r)?.hash_to_field_var(&pp.h)?,
                    nonce,
                )?)
            })?
        );

        println!("Total: {}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use ark_bn254::{Bn254, Fr};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalSerialize;
    use rand::thread_rng;

    use super::*;
    use crate::{
        primitives::poseidon::{Encryption, HField},
        proofs::ProofSystem,
        protocols::TK,
    };

    #[test]
    fn test_decrypt() {
        let rng = &mut ark_std::test_rng();

        let pp = &Params::<Bn254>::default();

        let esk_s = ark_secp256k1::Fr::rand(rng);
        let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();

        let ask_r = ark_secp256k1::Fr::rand(rng);
        let apk_r = (ark_secp256k1::Affine::generator() * ask_r).into_affine();

        let mut m = vec![];
        for _ in 0..3 {
            m.push(Fr::rand(rng));
        }
        let dk = (apk_r * esk_s).hash_to_field(&pp.h);
        let nonce = Fr::rand(rng);

        let c = Encryption::encrypt(&pp.h, m.clone(), dk, nonce);

        let now = Instant::now();
        for _ in 0..10000 {
            let dk = (epk_s * ask_r).hash_to_field(&pp.h);
            assert_eq!(m, Encryption::decrypt(&pp.h, c.clone(), dk, nonce).unwrap());
        }
        println!("{:?}", now.elapsed());
    }

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let esk_s = ark_secp256k1::Fr::rand(rng);
        let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();

        let apk_r = ark_secp256k1::Affine::rand(rng);
        let h_apk_r = apk_r.hash_to_field(&pp.h);

        let v = Fr::rand(rng);
        let rho_pt_r = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let pt_r = TK::pt_gen(pp, h_apk_r, v, rho_pt_r);

        let dk = (apk_r * esk_s).hash_to_field(&pp.h);
        let extra = Encryption::encrypt(&pp.h, vec![v, rho_pt_r], dk, nonce);

        let r_v = Fr::rand(rng);

        let s = Statement { pt_r, extra, epk_s, nonce };
        let w = Witness { v, apk_r, rho_pt_r, esk_s };

        let link_v = [r_v];

        let crs = ProofSystem::<_, RecvCircuit<_>>::setup(&pp, rng).unwrap();

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

        b.iter(|| ProofSystem::<_, RecvCircuit<_>>::setup(&pp, rng).unwrap());
    }

    #[bench]
    fn bench_prove(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let esk_s = ark_secp256k1::Fr::rand(rng);
        let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();

        let apk_r = ark_secp256k1::Affine::rand(rng);
        let h_apk_r = apk_r.hash_to_field(&pp.h);

        let v = Fr::rand(rng);
        let rho_pt_r = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let pt_r = TK::pt_gen(pp, h_apk_r, v, rho_pt_r);

        let dk = (apk_r * esk_s).hash_to_field(&pp.h);
        let extra = Encryption::encrypt(&pp.h, vec![v, rho_pt_r], dk, nonce);

        let r_v = Fr::rand(rng);

        let s = Statement { pt_r, extra, epk_s, nonce };
        let w = Witness { v, apk_r, rho_pt_r, esk_s };

        let link_v = [r_v];

        let crs = ProofSystem::<_, RecvCircuit<_>>::setup(&pp, rng).unwrap();

        b.iter(|| crs.prove(s.clone(), w.clone(), &link_v, rng).unwrap());
    }

    #[bench]
    fn bench_verify(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let esk_s = ark_secp256k1::Fr::rand(rng);
        let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();

        let apk_r = ark_secp256k1::Affine::rand(rng);
        let h_apk_r = apk_r.hash_to_field(&pp.h);

        let v = Fr::rand(rng);
        let rho_pt_r = Fr::rand(rng);
        let nonce = Fr::rand(rng);

        let pt_r = TK::pt_gen(pp, h_apk_r, v, rho_pt_r);

        let dk = (apk_r * esk_s).hash_to_field(&pp.h);
        let extra = Encryption::encrypt(&pp.h, vec![v, rho_pt_r], dk, nonce);

        let r_v = Fr::rand(rng);

        let s = Statement { pt_r, extra, epk_s, nonce };
        let w = Witness { v, apk_r, rho_pt_r, esk_s };

        let link_v = [r_v];

        let crs = ProofSystem::<_, RecvCircuit<_>>::setup(&pp, rng).unwrap();

        let proof_link = crs.prove(s.clone(), w, &link_v, rng).unwrap();

        b.iter(|| crs.verify(&s, &proof_link).unwrap())
    }
}
