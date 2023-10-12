use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use ark_relations::r1cs::SynthesisError;
use rand::Rng;

use super::{GlobalCRS, Params, SecretToken, SN};
use crate::{
    lego::ProofWithLink,
    primitives::{
        mt::IndexedMT,
        poseidon::{Encryption, HField},
    },
    proofs::{custom::PourCustomWitness, pt_form, recv, sn_form, Circuit, ProofSystem},
};

pub struct Proof<E: Pairing> {
    pub pt_form: Vec<ProofWithLink<E>>,
    pub sn_form: Vec<(E::ScalarField, ProofWithLink<E>)>,
    pub recv: Vec<(recv::Statement<E::ScalarField>, ProofWithLink<E>)>,
    pub value: ProofWithLink<E>,
}

pub struct Pour {}

impl Pour {
    pub fn prove<'a, R: Rng, E: Pairing, C: Circuit<'a, E>, const M: usize, const N: usize>(
        pp: &Params<E>,
        crs: &GlobalCRS<E>,
        custom_crs: &ProofSystem<'a, E, C>,
        rng: &mut R,
        pt_tree: &IndexedMT<E::ScalarField, 32>,
        sn_tree: &IndexedMT<E::ScalarField, 32>,
        sender_tokens: &[(ark_secp256k1::Fr, SecretToken<E::ScalarField>, E::ScalarField); M],
        receiver_tokens: &[(ark_secp256k1::Affine, SecretToken<E::ScalarField>, E::ScalarField); N],
        custom_statement: C::Statement,
    ) -> Result<Proof<E>, SynthesisError>
    where
        C::Witness: PourCustomWitness<E::ScalarField, M, N>,
    {
        let pt_acc = pt_tree.root();
        let sn_acc = sn_tree.root();

        let vec_r_v_s = (0..M).map(|_| E::ScalarField::rand(rng)).collect::<Vec<_>>();
        let vec_r_v_r = (0..N).map(|_| E::ScalarField::rand(rng)).collect::<Vec<_>>();
        let vec_r_pt_s = (0..M).map(|_| E::ScalarField::rand(rng)).collect::<Vec<_>>();
        let vec_r_h_apk_s = (0..M).map(|_| E::ScalarField::rand(rng)).collect::<Vec<_>>();

        Ok(Proof {
            pt_form: sender_tokens
                .iter()
                .zip(&vec_r_v_s)
                .zip(&vec_r_pt_s)
                .zip(&vec_r_h_apk_s)
                .map(|(((&(ask, st, pt), &r_v), &r_pt), &r_h_apk)| {
                    let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

                    crs.pt_form.prove(
                        pt_form::Statement { pt_acc },
                        pt_form::Witness {
                            pt,
                            v: st.v,
                            h_apk,
                            rho: st.rho,
                            pt_mem: pt_tree.prove(pt),
                        },
                        &[r_v, r_pt, r_h_apk],
                        rng,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?,
            sn_form: sender_tokens
                .iter()
                .zip(&vec_r_pt_s)
                .zip(&vec_r_h_apk_s)
                .map(|((&(ask, _, pt), &r_pt), &r_h_apk)| {
                    let sn = SN::sn_gen(pp, &ask, pt);

                    let h_apk = (ark_secp256k1::Affine::generator() * ask).hash_to_field(&pp.h);

                    Ok((
                        sn,
                        crs.sn_form.prove(
                            sn_form::Statement { sn_acc, sn_is_public: true, sn_public: sn },
                            sn_form::Witness { sn, ask, pt, h_apk, sn_nonmem: sn_tree.prove(sn) },
                            &[r_pt, r_h_apk],
                            rng,
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?,
            recv: receiver_tokens
                .iter()
                .zip(&vec_r_v_r)
                .map(|(&(apk_r, st_r, pt_r), &r_v)| {
                    let nonce = E::ScalarField::rand(rng);
                    let esk_s = ark_secp256k1::Fr::rand(rng);
                    let epk_s = (ark_secp256k1::Affine::generator() * esk_s).into_affine();
                    let dk = (apk_r * esk_s).hash_to_field(&pp.h);
                    let extra = Encryption::encrypt(&pp.h, vec![st_r.v, st_r.rho], dk, nonce);

                    let s_recv = recv::Statement { pt_r, extra, epk_s, nonce };

                    Ok((
                        s_recv.clone(),
                        crs.recv.prove(
                            s_recv,
                            recv::Witness { v: st_r.v, apk_r, rho_pt_r: st_r.rho, esk_s },
                            &[r_v],
                            rng,
                        )?,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?,
            value: custom_crs.prove(
                custom_statement,
                PourCustomWitness::new(
                    sender_tokens.map(|(_, t, _)| t.v),
                    receiver_tokens.map(|(_, t, _)| t.v),
                ),
                &[vec_r_v_s, vec_r_v_r].concat(),
                rng,
            )?,
        })
    }

    pub fn verify<'a, E: Pairing, C: Circuit<'a, E>>(
        crs: &GlobalCRS<E>,
        custom_crs: &ProofSystem<'a, E, C>,
        pt_tree: &IndexedMT<E::ScalarField, 32>,
        sn_tree: &IndexedMT<E::ScalarField, 32>,
        custom_statement: &C::Statement,
        pi: &Proof<E>,
    ) -> Result<bool, SynthesisError> {
        let pt_acc = pt_tree.root();
        let sn_acc = sn_tree.root();

        Ok(pi
            .pt_form
            .iter()
            .all(|pi| crs.pt_form.verify(&pt_form::Statement { pt_acc }, &pi).unwrap_or(false))
            && pi.sn_form.iter().all(|(sn, pi)| {
                crs.sn_form
                    .verify(&sn_form::Statement { sn_acc, sn_is_public: true, sn_public: *sn }, &pi)
                    .unwrap_or(false)
            })
            && pi.recv.iter().all(|(s_recv, pi)| crs.recv.verify(&s_recv, &pi).unwrap_or(false))
            && custom_crs.verify(&custom_statement, &pi.value)?)
    }
}

#[cfg(test)]
mod tests {
    use std::error::Error;

    use ark_bn254::{Bn254, Fr};
    use ark_ec::AffineRepr;
    use ark_ff::UniformRand;
    use rand::thread_rng;

    use super::*;
    use crate::{proofs::custom::sum::SumCircuit, protocols::mint::mint};

    const M: usize = 5;
    const N: usize = 3;

    #[test]
    fn test() -> Result<(), Box<dyn Error>> {
        let rng = &mut thread_rng();
        let pp = &Params::default();

        let crs = GlobalCRS::<Bn254>::setup(pp, rng)?;
        let custom_srs = ProofSystem::<_, SumCircuit<_, M, N>>::setup(&pp, rng)?;

        let inputs = [Fr::default(); M].map(|_| Fr::rand(rng));
        let mut outputs = [Fr::default(); N].map(|_| Fr::rand(rng));
        outputs[0] = inputs.iter().sum::<Fr>() - outputs.iter().skip(1).sum::<Fr>();

        let mut pt_tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            pt_tree.insert(Fr::rand(rng));
        }

        let mut sn_tree = IndexedMT::<_, 32>::new(&pp.h);
        for _ in 0..100 {
            sn_tree.insert(Fr::rand(rng));
        }

        let sender_tokens = inputs.map(|v| {
            let ask_s = ark_secp256k1::Fr::rand(rng);
            let apk_s = (ark_secp256k1::Affine::generator() * ask_s).into_affine();
            let (st_s, pt_s) = mint(pp, rng, &apk_s, v);
            pt_tree.insert(pt_s);
            (ask_s, st_s, pt_s)
        });
        let receiver_tokens = outputs.map(|v| {
            let ask_r = ark_secp256k1::Fr::rand(rng);
            let apk_r = (ark_secp256k1::Affine::generator() * ask_r).into_affine();
            let (st_r, pt_r) = mint(pp, rng, &apk_r, v);
            pt_tree.insert(pt_r);
            (apk_r, st_r, pt_r)
        });

        let pi = Pour::prove(
            pp,
            &crs,
            &custom_srs,
            rng,
            &pt_tree,
            &sn_tree,
            &sender_tokens,
            &receiver_tokens,
            (),
        )?;
        assert!(Pour::verify(&crs, &custom_srs, &pt_tree, &sn_tree, &(), &pi)?);
        Ok(())
    }
}
