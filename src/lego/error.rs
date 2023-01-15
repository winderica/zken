use ark_relations::r1cs::SynthesisError;

#[derive(Clone, Debug, PartialEq)]
pub enum Error {
    SynthesisError(SynthesisError),
    VectorLongerThanExpected(usize, usize),
    InvalidProof,
    InvalidLinkCommitment,
    InvalidWitnessCommitment,
    InsufficientWitnessesForCommitment(usize, usize),
}

impl From<SynthesisError> for Error {
    fn from(e: SynthesisError) -> Self {
        Self::SynthesisError(e)
    }
}
