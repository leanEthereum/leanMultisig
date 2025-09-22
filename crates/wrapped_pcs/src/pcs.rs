use p3_field::{ExtensionField, Field, TwoAdicField};
use serde::{Deserialize, Serialize};
use utils::{
    FSProver, FSVerifier, MY_DIGEST_ELEMS, MerkleCompress, MerkleHasher, PF, WhirParsedCommitment,
    WhirWitness,
};
use whir_p3::{
    dft::EvalsDft,
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::{evals::EvaluationsList, multilinear::Evaluation},
    whir::{
        committer::reader::ParsedCommitment,
        config::{WhirConfig, WhirConfigBuilder},
    },
};

pub trait NumVariables {
    fn num_variables(&self) -> usize;
}

pub trait PCS<F: Field, EF: ExtensionField<F>> {
    type ParsedCommitment: NumVariables;
    type Witness: Sync + Send;
    fn commit(
        &self,
        dft: &EvalsDft<PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        polynomial: &[F],
    ) -> Self::Witness;
    fn open(
        &self,
        dft: &EvalsDft<PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        statement: Vec<Evaluation<EF>>,
        dot_product_statement: Option<(Vec<EF>, EF)>,
        witness: Self::Witness,
        polynomial: &[F],
    );
    fn parse_commitment(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        num_variables: usize,
    ) -> Result<Self::ParsedCommitment, ProofError>;
    fn verify(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        parsed_commitment: &Self::ParsedCommitment,
        statements: Vec<Evaluation<EF>>,
    ) -> Result<(), ProofError>;
}

impl<F, EF, const DIGEST_ELEMS: usize> NumVariables for ParsedCommitment<F, EF, DIGEST_ELEMS>
where
    F: Field,
    EF: ExtensionField<F>,
{
    fn num_variables(&self) -> usize {
        self.num_variables
    }
}

impl<F, EF, H, C> PCS<F, EF> for WhirConfigBuilder<H, C, MY_DIGEST_ELEMS>
where
    PF<EF>: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField + ExtensionField<PF<EF>>,
    F: TwoAdicField + ExtensionField<PF<EF>>,
    H: MerkleHasher<EF>,
    C: MerkleCompress<EF>,
    [PF<EF>; MY_DIGEST_ELEMS]: Serialize + for<'de> Deserialize<'de>,
{
    type ParsedCommitment = WhirParsedCommitment<F, EF>;
    type Witness = WhirWitness<F, EF>;

    fn commit(
        &self,
        dft: &EvalsDft<PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        polynomial: &[F],
    ) -> Self::Witness {
        WhirConfig::new(self.clone(), polynomial.num_variables()).commit(
            dft,
            prover_state,
            polynomial,
        )
    }

    fn open(
        &self,
        dft: &EvalsDft<PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        statement: Vec<Evaluation<EF>>,
        dot_product_statement: Option<(Vec<EF>, EF)>,
        witness: Self::Witness,
        polynomial: &[F],
    ) {
        WhirConfig::new(self.clone(), polynomial.num_variables()).prove(
            dft,
            prover_state,
            statement,
            dot_product_statement,
            witness,
            polynomial,
        );
    }
    fn parse_commitment(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        num_variables: usize,
    ) -> Result<Self::ParsedCommitment, ProofError> {
        WhirConfig::new(self.clone(), num_variables).parse_commitment(verifier_state)
    }

    fn verify(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        parsed_commitment: &Self::ParsedCommitment,
        statements: Vec<Evaluation<EF>>,
    ) -> Result<(), ProofError> {
        WhirConfig::new(self.clone(), parsed_commitment.num_variables()).verify(
            verifier_state,
            parsed_commitment,
            statements,
            None,
        )?;
        Ok(())
    }
}
