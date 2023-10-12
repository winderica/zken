use core::ops::{AddAssign, Neg};

use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_relations::r1cs::SynthesisError;

use super::{
    link::{PESubspaceSnark, SubspaceSnark},
    PreparedVerifyingKey, Proof, ProofWithLink, VerifyingKey, VerifyingKeyWithLink,
};

/// Prepare the verifying key `vk` for use in proof verification.
pub fn prepare_verifying_key<E: Pairing>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    PreparedVerifyingKey {
        vk: vk.clone(),
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2).0,
        gamma_g2_neg_pc: vk.gamma_g2.into_group().neg().into_affine().into(),
        delta_g2_neg_pc: vk.delta_g2.into_group().neg().into_affine().into(),
    }
}

/// Prepare proof inputs for use with [`verify_proof_with_prepared_inputs`], wrt the prepared
/// verification key `pvk` and instance public inputs.
pub fn prepare_inputs<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    public_inputs: &[E::ScalarField],
) -> Result<E::G1, SynthesisError> {
    if (public_inputs.len() + 1) > pvk.vk.gamma_abc_g1.len() {
        return Err(SynthesisError::MalformedVerifyingKey).map_err(|e| e.into());
    }

    let mut d = pvk.vk.gamma_abc_g1[0].into_group();
    for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1)) {
        d.add_assign(&b.mul_bigint(i.into_bigint()));
    }

    Ok(d)
}

/// Verify the proof of the Subspace Snark on the equality of openings of cp_link and proof.d
pub fn verify_link_proof<E: Pairing>(
    vk: &VerifyingKeyWithLink<E>,
    proof: &ProofWithLink<E>,
) -> bool {
    let mut commitments = proof.link_d.to_vec();
    commitments.push(proof.groth16_proof.d);
    PESubspaceSnark::<E>::verify(&vk.link_pp, &vk.link_vk, &commitments, &proof.link_pi)
}

pub fn verify_qap_proof<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    a: E::G1Affine,
    b: E::G2Affine,
    c: E::G1Affine,
    d: E::G1Affine,
) -> Result<bool, SynthesisError> {
    let qap = E::multi_miller_loop(
        [a, c, d],
        [b.into(), pvk.delta_g2_neg_pc.clone(), pvk.gamma_g2_neg_pc.clone()],
    );

    Ok(E::final_exponentiation(qap).ok_or(SynthesisError::UnexpectedIdentity)?.0
        == pvk.alpha_g1_beta_g2)
}

/// Verify a LegoGroth16 proof `proof` against the prepared verification key `pvk`
pub fn verify_proof<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::ScalarField],
) -> Result<bool, SynthesisError> {
    let mut d = proof.d.into_group();
    d.add_assign(prepare_inputs(pvk, public_inputs)?);

    verify_qap_proof(pvk, proof.a, proof.b, proof.c, d.into_affine())
}

/// Verify a LegoGroth16 proof `proof` against the prepared verification key `pvk`
pub fn verify_proof_incl_cp_link<E: Pairing>(
    pvk: &PreparedVerifyingKey<E>,
    vk: &VerifyingKeyWithLink<E>,
    proof: &ProofWithLink<E>,
    public_inputs: &[E::ScalarField],
) -> Result<bool, SynthesisError> {
    Ok(verify_link_proof(vk, proof) && verify_proof(pvk, &proof.groth16_proof, public_inputs)?)
}
