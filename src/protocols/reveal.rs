use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use ark_relations::r1cs::SynthesisError;
use rand::Rng;

use super::{GlobalCRS, Params, SecretToken, SN};
use crate::{
    lego::ProofWithLink,
    primitives::{mt::IndexedMT, poseidon::HField},
    proofs::{bind_id, custom::RevealCustomWitness, pt_form, sn_form, Circuit, ProofSystem},
};

pub struct Proof<E: Pairing> {
    pub sn_form: ProofWithLink<E>,
    pub pt_form: ProofWithLink<E>,
    pub range: ProofWithLink<E>,
    pub bind_id: ProofWithLink<E>,
}

pub struct Reveal {}

impl Reveal {
    pub fn prove<'a, R: Rng, E: Pairing, C: Circuit<'a, E>>(
        pp: &Params<E>,
        crs: &GlobalCRS<E>,
        custom_crs: &ProofSystem<'a, E, C>,
        rng: &mut R,
        pt_tree: &IndexedMT<E::ScalarField, 32>,
        sn_tree: &IndexedMT<E::ScalarField, 32>,
        ask: ark_secp256k1::Fr,
        st: SecretToken<E::ScalarField>,
        pt: E::ScalarField,
        wsk: ark_secp256k1::Fr,
        delta: ark_secp256k1::Fr,
        custom_statement: C::Statement,
    ) -> Result<Proof<E>, SynthesisError>
    where
        C::Witness: RevealCustomWitness<E::ScalarField>,
    {
        let SecretToken { v, rho: rho_pt } = st;
        let wpk = (ark_secp256k1::Affine::generator() * wsk).into_affine();

        let sn = SN::sn_gen(pp, &ask, pt);
        let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

        let r_v = E::ScalarField::rand(rng);
        let r_pt = E::ScalarField::rand(rng);
        let r_h_apk = E::ScalarField::rand(rng);

        let pt_acc = pt_tree.root();
        let sn_acc = sn_tree.root();

        Ok(Proof {
            pt_form: crs.pt_form.prove(
                pt_form::Statement { pt_acc },
                pt_form::Witness { pt, v, h_apk, rho: rho_pt, pt_mem: pt_tree.prove(pt) },
                &[r_v, r_pt, r_h_apk],
                rng,
            )?,
            sn_form: crs.sn_form.prove(
                sn_form::Statement { sn_acc, sn_is_public: false, sn_public: Default::default() },
                sn_form::Witness { sn, ask, pt, h_apk, sn_nonmem: sn_tree.prove(sn) },
                &[r_pt, r_h_apk],
                rng,
            )?,
            range: custom_crs.prove(custom_statement, RevealCustomWitness::new(v), &[r_v], rng)?,
            bind_id: crs.bind_id.prove(
                bind_id::Statement { wpk },
                bind_id::Witness { h_apk, delta, wsk },
                &[r_h_apk],
                rng,
            )?,
        })
    }

    pub fn verify<'a, E: Pairing, C: Circuit<'a, E>>(
        crs: &GlobalCRS<E>,
        custom_crs: &ProofSystem<'a, E, C>,
        pt_tree: &IndexedMT<E::ScalarField, 32>,
        sn_tree: &IndexedMT<E::ScalarField, 32>,
        wpk: ark_secp256k1::Affine,
        custom_statement: &C::Statement,
        pi: &Proof<E>,
    ) -> Result<bool, SynthesisError> {
        let pt_acc = pt_tree.root();
        let sn_acc = sn_tree.root();

        Ok(crs.pt_form.verify(&pt_form::Statement { pt_acc }, &pi.pt_form)?
            && crs.sn_form.verify(
                &sn_form::Statement { sn_acc, sn_is_public: false, sn_public: Default::default() },
                &pi.sn_form,
            )?
            && crs.bind_id.verify(&bind_id::Statement { wpk }, &pi.bind_id)?
            && custom_crs.verify(&custom_statement, &pi.range)?)
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use ark_bn254::{Bn254, Fr};
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{BigInteger, PrimeField};
    use num::bigint::RandBigInt;
    use rand::thread_rng;

    use super::*;
    use crate::{
        primitives::poseidon::CRH,
        proofs::custom::range::{self, RangeCircuit},
        protocols::mint::mint,
    };

    #[test]
    fn test() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();
        let pp = &Params::default();

        let crs = GlobalCRS::<Bn254>::setup(pp, rng)?;
        let custom_srs = ProofSystem::<_, RangeCircuit<_>>::setup(&pp, rng)?;

        let (v_lb, v_ub) = {
            let l = Fr::from(rng.gen_biguint_below(&Fr::MODULUS_MINUS_ONE_DIV_TWO.into()));
            let u = Fr::from(rng.gen_biguint_below(&Fr::MODULUS_MINUS_ONE_DIV_TWO.into()));

            (l.min(u), l.max(u))
        };

        let v = Fr::from(rng.gen_biguint_range(&v_lb.into(), &v_ub.into()));

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
        let apk = (ark_secp256k1::Affine::generator() * ask).into_affine();

        let (st, pt) = mint(pp, rng, &apk, v);

        let mut pt_tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            pt_tree.insert(Fr::rand(rng));
        }
        pt_tree.insert(pt);

        let mut sn_tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            sn_tree.insert(Fr::rand(rng));
        }

        let range_check = range::Statement { l: v_lb, u: v_ub };

        let pi = Reveal::prove(
            pp,
            &crs,
            &custom_srs,
            rng,
            &pt_tree,
            &sn_tree,
            ask,
            st,
            pt,
            wsk,
            delta,
            range_check.clone(),
        )?;
        assert!(Reveal::verify(&crs, &custom_srs, &pt_tree, &sn_tree, wpk, &range_check, &pi)?);
        Ok(())
    }
}
