use std::cmp::Ordering;

use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean, fields::fp::FpVar, prelude::EqGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use serde::{Deserialize, Serialize};

use crate::{
    constants::W,
    primitives::{
        mt::{
            constraints::{IndexedMTGadget, IndexedMTProofVar},
            IndexedMTProof,
        },
        poseidon::HFieldGadget,
        secp256k1::constraints::{Secp256k1Gadget, SecretKeyVar},
    },
    proofs::Circuit,
    protocols::{Params, SNGadget},
    utils::num_constraints,
};

#[derive(Clone, Default)]
pub struct Witness<F: PrimeField> {
    pub h_apk: F,
    pub sn: F,
    pub pt: F,
    pub ask: ark_secp256k1::Fr,
    pub sn_nonmem: IndexedMTProof<F, 32>,
}

#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Statement<F: PrimeField> {
    pub sn_acc: F,
    pub sn_is_public: bool,
    pub sn_public: F,
}

pub struct SNCircuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub w: Witness<E::ScalarField>,
    pub s: Statement<E::ScalarField>,
}

impl<'a, E: Pairing> Circuit<'a, E> for SNCircuit<'a, E> {
    const NUM_COMMIT_WITNESSES: usize = 2;
    const NAME: &'static str = "SN";
    type Statement = Statement<E::ScalarField>;
    type Witness = Witness<E::ScalarField>;

    fn new(pp: &'a Params<E>, s: Self::Statement, w: Self::Witness) -> Self {
        Self { pp, s, w }
    }

    fn inputize(s: &Self::Statement) -> Vec<E::ScalarField> {
        vec![s.sn_acc, E::ScalarField::from(s.sn_is_public), s.sn_public]
    }
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for SNCircuit<'a, E> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<E::ScalarField>,
    ) -> ark_relations::r1cs::Result<()> {
        let Self { pp, w, s } = self;
        let Statement { sn_acc, sn_is_public, sn_public } = s;
        let Witness { h_apk, sn, ask, pt, sn_nonmem } = w;

        let pt = FpVar::new_witness(cs.clone(), || Ok(pt))?;
        let h_apk = FpVar::new_witness(cs.clone(), || Ok(h_apk))?;
        let sn = FpVar::new_witness(cs.clone(), || Ok(sn))?;
        let ask = SecretKeyVar::new_witness(cs.clone(), || Ok(ask))?;
        let sn_nonmem = IndexedMTProofVar::new_witness(cs.clone(), || Ok(sn_nonmem))?;

        let sn_acc = FpVar::new_input(cs.clone(), || Ok(sn_acc))?;
        let sn_is_public = Boolean::new_input(cs.clone(), || Ok(sn_is_public))?;
        let sn_public = FpVar::new_input(cs.clone(), || Ok(sn_public))?;

        sn_is_public.not().or(&sn.is_eq(&sn_public)?)?.enforce_equal(&Boolean::TRUE)?;

        println!("Shape check: {}", cs.num_constraints());

        println!(
            "PK generation: {}",
            num_constraints(&cs, || {
                Secp256k1Gadget::pk_gen::<_, W>(&ask)?
                    .hash_to_field_var(&pp.h)?
                    .enforce_equal(&h_apk)
            })?
        );

        println!("SN generation: {}", num_constraints(&cs, || SNGadget::sn_gen(pp, ask, pt))?);

        println!(
            "SN membership: {}",
            num_constraints(&cs, || {
                sn_nonmem.leaf.0.enforce_cmp_unchecked(&sn, Ordering::Less, false)?;
                sn_nonmem.leaf.1.enforce_cmp_unchecked(&sn, Ordering::Greater, false)?;
                sn_acc.enforce_equal(&IndexedMTGadget::calculate_root(&pp.h, &sn_nonmem)?)
            })?
        );

        println!("Total: {}", cs.num_constraints());

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Bn254, Fr};
    use ark_ec::AffineRepr;
    use ark_ff::UniformRand;
    use ark_serialize::CanonicalSerialize;
    use rand::thread_rng;

    use super::*;
    use crate::{
        primitives::{mt::IndexedMT, poseidon::HField},
        proofs::ProofSystem,
        protocols::SN,
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let ask = ark_secp256k1::Fr::rand(rng);

        let mut tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            tree.insert(Fr::rand(rng));
        }

        let pt = Fr::rand(rng);
        let sn = SN::sn_gen(pp, &ask, pt);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let s = Statement { sn_acc: tree.root(), sn_is_public: false, sn_public: Fr::rand(rng) };
        let w = Witness { sn, ask, pt, h_apk, sn_nonmem: tree.prove(sn) };
        let link_v = [r_pt, r_h_apk];

        let crs = ProofSystem::<_, SNCircuit<_>>::setup(&pp, rng).unwrap();

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

        b.iter(|| ProofSystem::<_, SNCircuit<_>>::setup(&pp, rng).unwrap());
    }

    #[bench]
    fn bench_prove(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let ask = ark_secp256k1::Fr::rand(rng);

        let mut tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            tree.insert(Fr::rand(rng));
        }

        let pt = Fr::rand(rng);
        let sn = SN::sn_gen(pp, &ask, pt);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let s = Statement { sn_acc: tree.root(), sn_is_public: false, sn_public: Fr::rand(rng) };
        let w = Witness { sn, ask, pt, h_apk, sn_nonmem: tree.prove(sn) };
        let link_v = [r_pt, r_h_apk];

        let crs = ProofSystem::<_, SNCircuit<_>>::setup(&pp, rng).unwrap();

        b.iter(|| crs.prove(s.clone(), w.clone(), &link_v, rng).unwrap());
    }

    #[bench]
    fn bench_verify(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let ask = ark_secp256k1::Fr::rand(rng);

        let mut tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            tree.insert(Fr::rand(rng));
        }

        let pt = Fr::rand(rng);
        let sn = SN::sn_gen(pp, &ask, pt);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let s = Statement { sn_acc: tree.root(), sn_is_public: false, sn_public: Fr::rand(rng) };
        let w = Witness { sn, ask, pt, h_apk, sn_nonmem: tree.prove(sn) };
        let link_v = [r_pt, r_h_apk];

        let crs = ProofSystem::<_, SNCircuit<_>>::setup(&pp, rng).unwrap();

        let proof_link = crs.prove(s.clone(), w, &link_v, rng).unwrap();

        b.iter(|| crs.verify(&s, &proof_link).unwrap())
    }
}
