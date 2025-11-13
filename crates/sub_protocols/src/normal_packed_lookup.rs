use multilinear_toolkit::prelude::*;
use utils::FSProver;
use utils::VecOrSlice;
use utils::dot_product_with_base;
use utils::transpose_slice_to_basis_coefficients;

use crate::GenericPackedLookupProver;
use crate::GenericPackedLookupVerifier;
use crate::PackedLookupStatements;

#[derive(Debug)]
pub struct NormalPackedLookupProver<'a, EF: ExtensionField<PF<EF>>> {
    generic: GenericPackedLookupProver<'a, PF<EF>, EF>,
}

impl<'a, EF: ExtensionField<PF<EF>>> NormalPackedLookupProver<'a, EF>
where
    PF<EF>: PrimeField64,
{
    pub fn pushforward_to_commit(&self) -> &[EF] {
        self.generic.pushforward_to_commit()
    }

    // before committing to the pushforward
    #[allow(clippy::too_many_arguments)]
    pub fn step_1(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        table: &'a [PF<EF>], // table[0] is assumed to be zero
        index_columns: Vec<&'a [PF<EF>]>,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        value_columns_base: Vec<&'a [PF<EF>]>,
        value_columns_extension: Vec<&'a [EF]>,
        statements: Vec<Vec<Evaluation<EF>>>,
        log_smallest_decomposition_chunk: usize,
    ) -> Self {
        assert_eq!(
            index_columns.len(),
            value_columns_base.len() + value_columns_extension.len()
        );
        let n_base_cols = value_columns_base.len();
        // let n_extension_cols = value_columns_extension.len();

        let mut all_value_columns = vec![];
        for col_base in value_columns_base {
            all_value_columns.push(vec![VecOrSlice::Slice(col_base)]);
        }
        for col_extension in &value_columns_extension {
            all_value_columns.push(
                transpose_slice_to_basis_coefficients::<PF<EF>, EF>(col_extension)
                    .into_iter()
                    .map(VecOrSlice::Vec)
                    .collect(),
            );
        }

        let mut multi_eval_statements = vec![];
        for eval_group in &statements[..n_base_cols] {
            multi_eval_statements.push(
                eval_group
                    .iter()
                    .map(|e| MultiEvaluation::new(e.point.clone(), vec![e.value]))
                    .collect(),
            );
        }

        for (eval_group, extension_column_split) in statements[n_base_cols..]
            .iter()
            .zip(&all_value_columns[n_base_cols..])
        {
            let mut multi_evals = vec![];
            for eval in eval_group {
                let sub_evals = extension_column_split
                    .par_iter()
                    .map(|slice| slice.as_slice().evaluate(&eval.point))
                    .collect::<Vec<_>>();
                // sanity check:
                assert_eq!(dot_product_with_base(&sub_evals), eval.value);

                prover_state.add_extension_scalars(&sub_evals);
                multi_evals.push(MultiEvaluation::new(eval.point.clone(), sub_evals));
            }

            multi_eval_statements.push(multi_evals);
        }

        let generic = GenericPackedLookupProver::step_1(
            prover_state,
            VecOrSlice::Slice(table),
            index_columns,
            heights,
            default_indexes,
            all_value_columns,
            multi_eval_statements,
            log_smallest_decomposition_chunk,
        );

        Self { generic }
    }

    // after committing to the pushforward
    pub fn step_2(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        non_zero_memory_size: usize,
    ) -> PackedLookupStatements<EF> {
        self.generic.step_2(prover_state, non_zero_memory_size)
    }
}

#[derive(Debug)]
pub struct NormalPackedLookupVerifier<EF: ExtensionField<PF<EF>>> {
    generic: GenericPackedLookupVerifier<EF>,
}

impl<EF: ExtensionField<PF<EF>>> NormalPackedLookupVerifier<EF>
where
    PF<EF>: PrimeField64,
{
    // before receiving the commitment to the pushforward
    pub fn step_1<TF: ExtensionField<PF<EF>>>(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        n_base_cols: usize,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        statements: Vec<Vec<Evaluation<EF>>>,
        log_smallest_decomposition_chunk: usize,
        table_initial_values: &[TF],
    ) -> ProofResult<Self>
    where
        EF: ExtensionField<TF>,
    {
        let mut multi_eval_statements = vec![];
        for eval_group in &statements[..n_base_cols] {
            multi_eval_statements.push(
                eval_group
                    .iter()
                    .map(|e| MultiEvaluation::new(e.point.clone(), vec![e.value]))
                    .collect(),
            );
        }

        for eval_group in &statements[n_base_cols..] {
            let mut multi_evals = vec![];
            for eval in eval_group {
                let sub_evals = verifier_state
                    .next_extension_scalars_vec(<EF as BasedVectorSpace<PF<EF>>>::DIMENSION)?;
                // sanity check:
                assert_eq!(dot_product_with_base(&sub_evals), eval.value);
                multi_evals.push(MultiEvaluation::new(eval.point.clone(), sub_evals));
            }

            multi_eval_statements.push(multi_evals);
        }

        let generic = GenericPackedLookupVerifier::step_1(
            verifier_state,
            heights,
            default_indexes,
            multi_eval_statements,
            log_smallest_decomposition_chunk,
            table_initial_values,
        )?;

        Ok(Self { generic })
    }

    // after receiving the commitment to the pushforward
    pub fn step_2(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        log_memory_size: usize,
    ) -> ProofResult<PackedLookupStatements<EF>> {
        self.generic.step_2(verifier_state, log_memory_size)
    }
}

fn expand_multi_evals<EF: Field>(
    statements: &[Vec<MultiEvaluation<EF>>],
) -> Vec<Vec<Evaluation<EF>>> {
    statements
        .iter()
        .flat_map(|multi_evals| {
            let mut evals = vec![vec![]; multi_evals[0].num_values()];
            for meval in multi_evals {
                for (i, &v) in meval.values.iter().enumerate() {
                    evals[i].push(Evaluation::new(meval.point.clone(), v));
                }
            }
            evals
        })
        .collect::<Vec<_>>()
}
