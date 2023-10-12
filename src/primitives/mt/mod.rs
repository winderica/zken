use std::{
    collections::{BTreeMap, HashMap},
    ops::Bound,
};

use ark_ff::PrimeField;
use num::Integer;

use super::poseidon::{HField, PoseidonParameters, CRH};

pub mod constraints;

#[derive(Clone)]
pub struct IndexedMTProof<F: PrimeField, const H: usize> {
    pub path: [F; H],
    pub index: usize,
    pub leaf: IndexedMTLeaf<F>,
}

impl<F: PrimeField, const H: usize> Default for IndexedMTProof<F, H> {
    fn default() -> Self {
        Self { path: [F::default(); H], index: Default::default(), leaf: Default::default() }
    }
}

#[derive(Default, Clone)]
pub struct IndexedMTLeaf<F: PrimeField>(F, F);

impl<F: PrimeField> HField<F> for IndexedMTLeaf<F> {
    fn hash_to_field(&self, pp: &PoseidonParameters<F>) -> F {
        CRH::hash(pp, self.0, self.1)
    }
}

pub struct IndexedMT<'a, F: PrimeField, const H: usize>
where
    [(); H + 1]: Sized,
{
    pub pp: &'a PoseidonParameters<F>,
    pub nodes: HashMap<(usize, usize), F>,
    pub values: BTreeMap<F, usize>,
    default_nodes: [F; H + 1],
}

impl<'a, F: PrimeField, const H: usize> IndexedMT<'a, F, H>
where
    [(); H + 1]: Sized,
{
    pub fn new(pp: &'a PoseidonParameters<F>) -> Self {
        let default_nodes = {
            let mut values = [IndexedMTLeaf::default().hash_to_field(&pp); H + 1];
            for i in (0..H).rev() {
                values[i] = CRH::<F>::hash(pp, values[i + 1], values[i + 1]);
            }
            values
        };
        Self {
            pp,
            nodes: HashMap::new(),
            default_nodes,
            values: BTreeMap::from([(F::default(), 0)]),
        }
    }

    fn update(&mut self, mut index: usize, mut value: F) {
        for j in (1..=H).rev() {
            self.nodes.insert((j, index), value);

            let sibling_value = *self.nodes.get(&(j, index ^ 1)).unwrap_or(&self.default_nodes[j]);
            let (left_value, right_value) =
                if index.is_even() { (value, sibling_value) } else { (sibling_value, value) };

            value = CRH::<F>::hash(&self.pp, left_value, right_value);
            index >>= 1;
        }
        self.nodes.insert((0, index), value);
    }

    pub fn insert(&mut self, value: F) {
        let index = self.values.len();
        assert!(index < 1 << H);
        let prev = self.values.upper_bound(Bound::Excluded(&value));
        let (&prev_value, &prev_index) = prev.key_value().unwrap();
        let (&next_value, _) = prev.peek_next().unwrap_or((&F::default(), &0));

        self.values.insert(value, index);

        self.update(index, IndexedMTLeaf(value, next_value).hash_to_field(&self.pp));
        self.update(prev_index, IndexedMTLeaf(prev_value, value).hash_to_field(&self.pp));
    }

    pub fn prove(&self, value: F) -> IndexedMTProof<F, H> {
        let prev = self.values.upper_bound(Bound::Included(&value));
        let (&prev_value, &prev_index) = prev.key_value().unwrap_or((&F::default(), &0));
        let next = self.values.lower_bound(Bound::Excluded(&value));
        let (&next_value, _) = next.key_value().unwrap_or((&F::default(), &0));

        let mut index = prev_index;

        let mut path = [F::default(); H];
        for j in (1..=H).rev() {
            path[H - j] = *self.nodes.get(&(j, index ^ 1)).unwrap_or(&self.default_nodes[j]);
            index >>= 1;
        }
        IndexedMTProof { path, index: prev_index, leaf: IndexedMTLeaf(prev_value, next_value) }
    }

    pub fn verify(pp: &PoseidonParameters<F>, root: F, proof: &IndexedMTProof<F, H>) -> bool {
        let mut value = proof.leaf.hash_to_field(pp);
        let mut index = proof.index;
        for &sibling_value in &proof.path {
            let (left_value, right_value) =
                if index.is_even() { (value, sibling_value) } else { (sibling_value, value) };
            value = CRH::<F>::hash(pp, left_value, right_value);
            index >>= 1;
        }
        value == root
    }

    pub fn root(&self) -> F {
        *self.nodes.get(&(0, 0)).unwrap_or(&self.default_nodes[0])
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Fr;

    use super::*;

    #[test]
    fn test_mt() {
        let pp = PoseidonParameters::<Fr>::default();
        let mut mt = IndexedMT::<Fr, 32>::new(&pp);
        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(0u64))));

        mt.insert(Fr::from(4u64));
        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(0u64))));
        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(4u64))));

        mt.insert(Fr::from(1u64));
        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(0u64))));
        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(4u64))));
        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(1u64))));

        mt.insert(Fr::from(3u64));

        mt.insert(Fr::from(2u64));

        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(1u64))));
        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(2u64))));
        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(3u64))));
        assert!(IndexedMT::verify(&pp, mt.root(), &mt.prove(Fr::from(4u64))));
    }
}
