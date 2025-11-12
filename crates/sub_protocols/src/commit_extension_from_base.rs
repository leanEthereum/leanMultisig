use crate::ColDims;
use multilinear_toolkit::prelude::*;
use utils::dot_product_with_base;
use utils::transpose_slice_to_basis_coefficients;

/// Commit extension field columns with a PCS allowing to commit in the base field

#[derive(Debug)]
pub struct ExtensionCommitmentFromBaseProver<EF: ExtensionField<PF<EF>>> {
    pub sub_columns_to_commit: Vec<Vec<PF<EF>>>,
}

pub fn committed_dims_extension_from_base<EF: ExtensionField<PF<EF>>>(
    non_zero_height: usize,
    default_value: EF,
) -> Vec<ColDims<PF<EF>>> {
    EF::as_basis_coefficients_slice(&default_value)
        .iter()
        .map(|&d| ColDims::padded(non_zero_height, d))
        .collect()
}

impl<EF: ExtensionField<PF<EF>>> ExtensionCommitmentFromBaseProver<EF> {
    pub fn before_commitment(extension_column: &[EF]) -> Self {
        let sub_columns_to_commit =
            transpose_slice_to_basis_coefficients::<PF<EF>, EF>(extension_column);
        Self {
            sub_columns_to_commit,
        }
    }

    pub fn after_commitment(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        evaluation_point: &MultilinearPoint<EF>,
    ) -> Vec<Vec<Evaluation<EF>>> {
        let sub_evals = self
            .sub_columns_to_commit
            .par_iter()
            .map(|slice| slice.evaluate(&evaluation_point))
            .collect::<Vec<_>>();

        prover_state.add_extension_scalars(&sub_evals);

        let statements_remaning_to_prove = sub_evals
            .iter()
            .map(|&sub_value| vec![Evaluation::new(evaluation_point.clone(), sub_value)])
            .collect::<Vec<_>>();

        statements_remaning_to_prove
    }
}

#[derive(Debug)]
pub struct ExtensionCommitmentFromBaseVerifier {}

impl ExtensionCommitmentFromBaseVerifier {
    pub fn after_commitment<EF: ExtensionField<PF<EF>>>(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        claim: &Evaluation<EF>,
    ) -> ProofResult<Vec<Vec<Evaluation<EF>>>> {
        let sub_evals = verifier_state.next_extension_scalars_vec(EF::DIMENSION)?;

        let statements_remaning_to_verify = sub_evals
            .iter()
            .map(|&sub_value| vec![Evaluation::new(claim.point.clone(), sub_value)])
            .collect::<Vec<_>>();

        if dot_product_with_base(&sub_evals) != claim.value {
            return Err(ProofError::InvalidProof);
        }

        Ok(statements_remaning_to_verify)
    }
}
