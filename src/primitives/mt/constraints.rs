use ark_ff::{BitIteratorLE, PrimeField};
use ark_r1cs_std::{
    boolean::Boolean,
    fields::fp::FpVar,
    prelude::{AllocVar, AllocationMode},
};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::vec::Vec;

use super::IndexedMTProof;
use crate::primitives::poseidon::{constraints::CRHGadget, HFieldGadget, PoseidonParameters};

pub struct IndexedMTLeafVar<F: PrimeField>(pub FpVar<F>, pub FpVar<F>);

impl<F: PrimeField> HFieldGadget<F> for IndexedMTLeafVar<F> {
    fn hash_to_field_var(&self, pp: &PoseidonParameters<F>) -> Result<FpVar<F>, SynthesisError> {
        CRHGadget::hash(pp, self.0.clone(), self.1.clone())
    }
}

pub struct IndexedMTProofVar<F: PrimeField, const H: usize> {
    pub path: [FpVar<F>; H],
    pub index: [Boolean<F>; H],
    pub leaf: IndexedMTLeafVar<F>,
}

impl<F: PrimeField, const H: usize> AllocVar<IndexedMTProof<F, H>, F> for IndexedMTProofVar<F, H> {
    fn new_variable<T: std::borrow::Borrow<IndexedMTProof<F, H>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let p = f().map(|g| g.borrow().to_owned())?;

        let path = Vec::new_variable(cs.clone(), || Ok(p.path), mode)?;
        let mut index = BitIteratorLE::new([p.index as u64]).collect::<Vec<_>>();
        index.resize(H, false);
        let index = Vec::new_variable(cs.clone(), || Ok(index), mode)?;
        let leaf = IndexedMTLeafVar(
            FpVar::new_variable(cs.clone(), || Ok(p.leaf.0), mode)?,
            FpVar::new_variable(cs.clone(), || Ok(p.leaf.1), mode)?,
        );

        Ok(Self { path: path.try_into().unwrap(), index: index.try_into().unwrap(), leaf })
    }
}

pub struct IndexedMTGadget;

impl IndexedMTGadget {
    pub fn calculate_root<F: PrimeField, const H: usize>(
        pp: &PoseidonParameters<F>,
        proof: &IndexedMTProofVar<F, H>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let mut curr_hash = proof.leaf.hash_to_field_var(pp)?;

        for (bit, sibling) in proof.index.iter().zip(proof.path.iter()) {
            let t = sibling + &curr_hash;
            let l = bit.select(sibling, &curr_hash)?;
            let r = t - &l;

            curr_hash = CRHGadget::hash(pp, l, r)?;
        }

        Ok(curr_hash)
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;
    use ark_r1cs_std::prelude::{AllocVar, EqGadget};
    use ark_relations::r1cs::ConstraintSystem;

    use super::*;
    use crate::primitives::mt::IndexedMT;

    fn merkle_tree_test(leaves: &[Fr]) -> () {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let pp = PoseidonParameters::<Fr>::default();
        let mut tree = IndexedMT::<Fr, 32>::new(&pp);
        for &leaf in leaves {
            tree.insert(leaf);
            let proof = tree.prove(leaf);
            assert!(IndexedMT::verify(&pp, tree.root(), &proof));

            let root = FpVar::new_witness(cs.clone(), || Ok(tree.root())).unwrap();

            assert!(IndexedMTGadget::calculate_root(
                &pp,
                &IndexedMTProofVar::new_witness(cs.clone(), || Ok(proof)).unwrap()
            )
            .map(|i| i.enforce_equal(&root))
            .is_ok());
            println!("{}", cs.num_constraints());
            assert!(cs.is_satisfied().unwrap());
        }
    }

    #[test]
    fn test_merkle_tree() {
        let leaves = vec![
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(4u64),
            Fr::from(5u64),
            Fr::from(6u64),
            Fr::from(7u64),
            Fr::from(8u64),
        ];
        merkle_tree_test(&leaves);
    }
}
