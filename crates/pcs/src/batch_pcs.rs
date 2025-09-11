use crate::pcs::PCS;
use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};
use serde::{Deserialize, Serialize};
use utils::{Evaluation, FSProver, FSVerifier, PF, PFPacking};
use whir_p3::{
    dft::EvalsDft,
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::evals::EvaluationsList,
    whir::{
        config::{FoldingFactor, WhirConfig, WhirConfigBuilder},
        prover::Prover,
        statement::Statement,
        verifier::Verifier,
    },
};

pub trait BatchPCS<FA: Field, FB: Field, EF: ExtensionField<FA> + ExtensionField<FB>> {
    type PcsA: PCS<FA, EF>;
    type PcsB: PCS<FB, EF>;

    fn pcs_a(&self) -> &Self::PcsA;

    fn pcs_b(&self, num_variables_a: usize, num_variables_b: usize) -> Self::PcsB;

    fn batch_open(
        &self,
        dft: &EvalsDft<PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        statements_a: &[Evaluation<EF>],
        witness_a: <Self::PcsA as PCS<FA, EF>>::Witness,
        polynomial_a: &[FA],
        statements_b: &[Evaluation<EF>],
        witness_b: <Self::PcsB as PCS<FB, EF>>::Witness,
        polynomial_b: &[FB],
    );

    fn batch_verify(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        parsed_commitment_a: &<Self::PcsA as PCS<FA, EF>>::ParsedCommitment,
        statements_a: &[Evaluation<EF>],
        parsed_commitment_b: &<Self::PcsB as PCS<FB, EF>>::ParsedCommitment,
        statements_b: &[Evaluation<EF>],
    ) -> Result<(), ProofError>;
}

#[derive(Debug)]
pub struct WhirBatchPcs<FA, FB, EF, H, C, const DIGEST_ELEMS: usize>(
    pub WhirConfigBuilder<FA, EF, H, C, DIGEST_ELEMS>,
    pub WhirConfigBuilder<FB, EF, H, C, DIGEST_ELEMS>,
);

impl<F, EF, H, C, const DIGEST_ELEMS: usize> BatchPCS<F, EF, EF>
    for WhirBatchPcs<F, EF, EF, H, C, DIGEST_ELEMS>
where
    PF<EF>: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField + ExtensionField<PF<EF>>,
    F: TwoAdicField + ExtensionField<PF<EF>>,
    H: CryptographicHasher<PF<EF>, [PF<EF>; DIGEST_ELEMS]>
        + CryptographicHasher<PFPacking<EF>, [PFPacking<EF>; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[PF<EF>; DIGEST_ELEMS], 2>
        + PseudoCompressionFunction<[PFPacking<EF>; DIGEST_ELEMS], 2>
        + Sync,
    [PF<EF>; DIGEST_ELEMS]: Serialize + for<'de> Deserialize<'de>,
{
    type PcsA = WhirConfigBuilder<F, EF, H, C, DIGEST_ELEMS>;
    type PcsB = WhirConfigBuilder<EF, EF, H, C, DIGEST_ELEMS>;

    fn pcs_a(&self) -> &Self::PcsA {
        &self.0
    }

    fn pcs_b(&self, num_variables_a: usize, num_variables_b: usize) -> Self::PcsB {
        let mut pcs_b = self.1.clone();
        let var_diff = num_variables_a.checked_sub(num_variables_b).unwrap();
        let initial_folding_factor_b = self
            .0
            .folding_factor
            .at_round(0)
            .checked_sub(var_diff)
            .unwrap();
        let new_folding_factor_b = FoldingFactor::ConstantFromSecondRound(
            initial_folding_factor_b,
            pcs_b.folding_factor.at_round(1),
        );
        pcs_b.folding_factor = new_folding_factor_b;
        pcs_b
    }

    fn batch_open(
        &self,
        dft: &EvalsDft<PF<EF>>,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        statements_a: &[Evaluation<EF>],
        witness_a: <Self::PcsA as PCS<F, EF>>::Witness,
        polynomial_a: &[F],
        statements_b: &[Evaluation<EF>],
        witness_b: <Self::PcsB as PCS<EF, EF>>::Witness,
        polynomial_b: &[EF],
    ) {
        // TODO need to improve inside WHIR repo

        let config_a = WhirConfig::new(self.0.clone(), polynomial_a.num_variables());
        let mut whir_statements_a = Statement::new(polynomial_a.num_variables());
        for statement in statements_a {
            whir_statements_a.add_constraint(statement.point.clone(), statement.value);
        }
        let mut whir_statements_b = Statement::new(polynomial_b.num_variables());
        for statement in statements_b {
            whir_statements_b.add_constraint(statement.point.clone(), statement.value);
        }
        Prover(&config_a)
            .batch_prove(
                dft,
                prover_state,
                whir_statements_a,
                witness_a,
                polynomial_a,
                whir_statements_b,
                witness_b,
                polynomial_b,
            )
            .unwrap();
    }

    fn batch_verify(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        parsed_commitment_a: &<Self::PcsA as PCS<F, EF>>::ParsedCommitment,
        statements_a: &[Evaluation<EF>],
        parsed_commitment_b: &<Self::PcsB as PCS<EF, EF>>::ParsedCommitment,
        statements_b: &[Evaluation<EF>],
    ) -> Result<(), ProofError> {
        let config = WhirConfig::new(self.0.clone(), parsed_commitment_a.num_variables);
        let mut whir_statements_a = Statement::new(parsed_commitment_a.num_variables);
        for statement in statements_a {
            whir_statements_a.add_constraint(statement.point.clone(), statement.value);
        }
        let mut whir_statements_b = Statement::new(parsed_commitment_b.num_variables);
        for statement in statements_b {
            whir_statements_b.add_constraint(statement.point.clone(), statement.value);
        }
        Verifier(&config).batch_verify(
            verifier_state,
            parsed_commitment_a,
            &whir_statements_a,
            parsed_commitment_b,
            &whir_statements_b,
        )?;
        Ok(())
    }
}
