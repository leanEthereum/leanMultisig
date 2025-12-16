use multilinear_toolkit::prelude::*;
use utils::dot_product_with_base;
use utils::transpose_slice_to_basis_coefficients;

/// Commit extension field columns with a PCS allowing to commit in the base field

#[derive(Debug)]
pub struct ExtensionCommitmentFromBaseProver<EF: ExtensionField<PF<EF>>> {
    pub sub_columns_to_commit: Vec<Vec<PF<EF>>>,
}

impl<EF: ExtensionField<PF<EF>>> ExtensionCommitmentFromBaseProver<EF> {
    pub fn before_commitment(extension_columns: Vec<&[EF]>) -> Self {
        let mut sub_columns_to_commit = Vec::new();
        for extension_column in extension_columns {
            sub_columns_to_commit.extend(transpose_slice_to_basis_coefficients::<PF<EF>, EF>(extension_column));
        }
        Self { sub_columns_to_commit }
    }

    pub fn after_commitment(
        &self,
        prover_state: &mut impl FSProver<EF>,
        evaluation_point: &MultilinearPoint<EF>,
    ) -> Vec<Vec<Evaluation<EF>>> {
        let sub_evals = self
            .sub_columns_to_commit
            .par_iter()
            .map(|sub_column| sub_column.evaluate(evaluation_point))
            .collect::<Vec<_>>();

        prover_state.add_extension_scalars(&sub_evals);

        sub_evals
            .iter()
            .map(|sub_value| vec![Evaluation::new(evaluation_point.clone(), *sub_value)])
            .collect::<Vec<_>>()
    }
}

#[derive(Debug)]
pub struct ExtensionCommitmentFromBaseVerifier {}

impl ExtensionCommitmentFromBaseVerifier {
    pub fn after_commitment<EF: ExtensionField<PF<EF>>>(
        verifier_state: &mut impl FSVerifier<EF>,
        claim: &MultiEvaluation<EF>,
    ) -> ProofResult<Vec<Vec<Evaluation<EF>>>> {
        let sub_evals = verifier_state.next_extension_scalars_vec(EF::DIMENSION * claim.num_values())?;

        let mut statements_remaning_to_verify = Vec::new();
        for (chunk, claim_value) in sub_evals.chunks_exact(EF::DIMENSION).zip(&claim.values) {
            if dot_product_with_base(chunk) != *claim_value {
                return Err(ProofError::InvalidProof);
            }
            statements_remaning_to_verify.extend(
                chunk
                    .iter()
                    .map(|&sub_value| vec![Evaluation::new(claim.point.clone(), sub_value)]),
            );
        }

        Ok(statements_remaning_to_verify)
    }
}
