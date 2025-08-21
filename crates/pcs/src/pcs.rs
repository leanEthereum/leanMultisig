use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
use serde::{Deserialize, Serialize};
use utils::{Evaluation, FSProver, FSVerifier, PF, PFPacking};
use whir_p3::{
    dft::EvalsDft,
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::evals::EvaluationsList,
    whir::{
        committer::{
            Witness,
            reader::{CommitmentReader, ParsedCommitment},
            writer::Commiter,
        },
        config::{WhirConfig, WhirConfigBuilder},
        prover::Prover,
        statement::Statement,
        verifier::Verifier,
    },
};

pub trait NumVariables {
    fn num_variables(&self) -> usize;
}

pub trait PCS<F: Field, EF: ExtensionField<F>> {
    type ParsedCommitment: NumVariables;
    type Witness;
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
        statements: &[Evaluation<EF>],
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
        statements: &[Evaluation<EF>],
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

impl<F, EF, H, C, const DIGEST_ELEMS: usize> PCS<F, EF>
    for WhirConfigBuilder<F, EF, H, C, DIGEST_ELEMS>
where
    F: TwoAdicField,
    PF<EF>: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField + ExtensionField<PF<EF>>,
    F: ExtensionField<PF<EF>>,
    H: CryptographicHasher<PF<EF>, [PF<EF>; DIGEST_ELEMS]>
        + CryptographicHasher<PFPacking<EF>, [PFPacking<EF>; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[PF<EF>; DIGEST_ELEMS], 2>
        + PseudoCompressionFunction<[PFPacking<EF>; DIGEST_ELEMS], 2>
        + Sync,
    [PF<EF>; DIGEST_ELEMS]: Serialize + for<'de> Deserialize<'de>,
{
    type ParsedCommitment = ParsedCommitment<F, EF, DIGEST_ELEMS>;
    type Witness = Witness<F, EF, DIGEST_ELEMS>;

    fn commit(
        &self,
        dft: &EvalsDft<PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        polynomial: &[F],
    ) -> Self::Witness {
        let config = WhirConfig::new(self.clone(), polynomial.num_variables());
        Commiter(&config)
            .commit(dft, prover_state, polynomial)
            .unwrap()
    }

    fn open(
        &self,
        dft: &EvalsDft<PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        statements: &[Evaluation<EF>],
        witness: Self::Witness,
        polynomial: &[F],
    ) {
        let config = WhirConfig::new(self.clone(), polynomial.num_variables());
        let mut whir_statements = Statement::new(polynomial.num_variables());
        for statement in statements {
            whir_statements.add_constraint(statement.point.clone(), statement.value);
        }
        Prover(&config)
            .prove(dft, prover_state, whir_statements, witness, polynomial)
            .unwrap();
    }
    fn parse_commitment(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        num_variables: usize,
    ) -> Result<Self::ParsedCommitment, ProofError> {
        let config = WhirConfig::new(self.clone(), num_variables);
        CommitmentReader(&config).parse_commitment(verifier_state)
    }

    fn verify(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        parsed_commitment: &Self::ParsedCommitment,
        statements: &[Evaluation<EF>],
    ) -> Result<(), ProofError> {
        let config = WhirConfig::new(self.clone(), parsed_commitment.num_variables());
        let mut whir_statements = Statement::new(parsed_commitment.num_variables());
        for statement in statements {
            whir_statements.add_constraint(statement.point.clone(), statement.value);
        }
        Verifier(&config).verify(verifier_state, parsed_commitment, &whir_statements)?;
        Ok(())
    }
}
