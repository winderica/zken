use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, prelude::EqGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use serde::{Deserialize, Serialize};

use crate::{
    constants::W,
    primitives::mt::{
        constraints::{IndexedMTGadget, IndexedMTProofVar},
        IndexedMTProof,
    },
    proofs::Circuit,
    protocols::{Params, TokenGadget},
    utils::num_constraints,
};

#[derive(Clone, Default)]
pub struct Witness<F: PrimeField> {
    pub pt: F,
    pub v: F,
    pub h_apk: F,
    pub rho: F,
    pub pt_mem: IndexedMTProof<F, 32>,
}

#[derive(Clone, Default, Serialize, Deserialize)]
pub struct Statement<F: PrimeField> {
    pub pt_acc: F,
}

pub struct PTCircuit<'a, E: Pairing> {
    pub pp: &'a Params<E>,
    pub w: Witness<E::ScalarField>,
    pub s: Statement<E::ScalarField>,
}

impl<'a, E: Pairing> Circuit<'a, E> for PTCircuit<'a, E> {
    const NUM_COMMIT_WITNESSES: usize = 3;
    const NAME: &'static str = "PT";
    type Statement = Statement<E::ScalarField>;
    type Witness = Witness<E::ScalarField>;

    fn new(pp: &'a Params<E>, s: Self::Statement, w: Self::Witness) -> Self {
        Self { pp, s, w }
    }

    fn inputize(s: &Self::Statement) -> Vec<E::ScalarField> {
        vec![s.pt_acc]
    }
}

impl<'a, E: Pairing> ConstraintSynthesizer<E::ScalarField> for PTCircuit<'a, E> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<E::ScalarField>,
    ) -> ark_relations::r1cs::Result<()> {
        let Self { pp, w, s } = self;
        let Statement { pt_acc } = s;
        let Witness { pt, v, h_apk, rho: rho_pt, pt_mem } = w;

        let v = FpVar::new_witness(cs.clone(), || Ok(v))?;
        let pt = FpVar::new_witness(cs.clone(), || Ok(pt))?;
        let h_apk = FpVar::new_witness(cs.clone(), || Ok(h_apk))?;
        let rho_pt = FpVar::new_witness(cs.clone(), || Ok(rho_pt))?;
        let pt_mem = IndexedMTProofVar::new_witness(cs.clone(), || Ok(pt_mem))?;

        let pt_acc = FpVar::new_input(cs.clone(), || Ok(pt_acc))?;

        println!("Shape check: {}", cs.num_constraints());

        println!(
            "PT generation: {}",
            num_constraints(&cs, || {
                pt.enforce_equal(&TokenGadget::pt_gen::<_, W>(pp, h_apk, v, rho_pt)?)
            })?
        );
        println!(
            "PT membership: {}",
            num_constraints(&cs, || {
                pt_acc.enforce_equal(&IndexedMTGadget::calculate_root(&pp.h, &pt_mem)?)?;
                pt_mem.leaf.0.enforce_equal(&pt)
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
        protocols::TK,
    };

    #[test]
    fn test() {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let ask = ark_secp256k1::Fr::rand(rng);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let v = Fr::rand(rng);
        let rho_pt = Fr::rand(rng);

        let mut tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            tree.insert(Fr::rand(rng));
        }

        let pt = TK::pt_gen(pp, h_apk, v, rho_pt);
        tree.insert(pt);

        let r_v = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let s = Statement { pt_acc: tree.root() };
        let w = Witness { pt, v, h_apk, rho: rho_pt, pt_mem: tree.prove(pt) };
        let link_v = [r_v, r_pt, r_h_apk];

        let crs = ProofSystem::<_, PTCircuit<_>>::setup(&pp, rng).unwrap();

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

        b.iter(|| ProofSystem::<_, PTCircuit<_>>::setup(&pp, rng).unwrap());
    }

    #[bench]
    fn bench_prove(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let ask = ark_secp256k1::Fr::rand(rng);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let v = Fr::rand(rng);
        let rho_pt = Fr::rand(rng);

        let mut tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            tree.insert(Fr::rand(rng));
        }

        let pt = TK::pt_gen(pp, h_apk, v, rho_pt);
        tree.insert(pt);

        let r_v = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let s = Statement { pt_acc: tree.root() };
        let w = Witness { pt, v, h_apk, rho: rho_pt, pt_mem: tree.prove(pt) };
        let link_v = [r_v, r_pt, r_h_apk];

        let crs = ProofSystem::<_, PTCircuit<_>>::setup(&pp, rng).unwrap();

        b.iter(|| crs.prove(s.clone(), w.clone(), &link_v, rng).unwrap());
    }

    #[bench]
    fn bench_verify(b: &mut test::Bencher) {
        let rng = &mut thread_rng();

        let pp = &Params::<Bn254>::default();

        let ask = ark_secp256k1::Fr::rand(rng);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let v = Fr::rand(rng);
        let rho_pt = Fr::rand(rng);

        let mut tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            tree.insert(Fr::rand(rng));
        }

        let pt = TK::pt_gen(pp, h_apk, v, rho_pt);
        tree.insert(pt);

        let r_v = Fr::rand(rng);
        let r_pt = Fr::rand(rng);
        let r_h_apk = Fr::rand(rng);

        let s = Statement { pt_acc: tree.root() };
        let w = Witness { pt, v, h_apk, rho: rho_pt, pt_mem: tree.prove(pt) };
        let link_v = [r_v, r_pt, r_h_apk];

        let crs = ProofSystem::<_, PTCircuit<_>>::setup(&pp, rng).unwrap();

        let proof_link = crs.prove(s.clone(), w, &link_v, rng).unwrap();

        b.iter(|| crs.verify(&s, &proof_link).unwrap())
    }
}
