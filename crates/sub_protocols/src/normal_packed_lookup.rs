use multilinear_toolkit::prelude::*;
use utils::FSProver;
use utils::VecOrSlice;
use utils::assert_eq_many;
use utils::dot_product_with_base;
use utils::transpose_slice_to_basis_coefficients;

use crate::GenericPackedLookupProver;
use crate::GenericPackedLookupVerifier;

#[derive(Debug)]
pub struct NormalPackedLookupProver<'a, EF: ExtensionField<PF<EF>>> {
    generic: GenericPackedLookupProver<'a, PF<EF>, EF>,
    n_cols_f: usize,
}

#[derive(Debug, PartialEq)]
pub struct NormalPackedLookupStatements<EF> {
    pub on_table: Evaluation<EF>,
    pub on_pushforward: Vec<Evaluation<EF>>,
    pub on_indexes_f: Vec<Vec<Evaluation<EF>>>, // contain sparse points (TODO take advantage of it)
    pub on_indexes_ef: Vec<Vec<Evaluation<EF>>>, // contain sparse points (TODO take advantage of it)
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
        index_columns_f: Vec<&'a [PF<EF>]>,
        index_columns_ef: Vec<&'a [PF<EF>]>,
        heights_f: Vec<usize>,
        heights_ef: Vec<usize>,
        default_indexes_f: Vec<usize>,
        default_indexes_ef: Vec<usize>,
        value_columns_f: Vec<&'a [PF<EF>]>,
        value_columns_ef: Vec<&'a [EF]>,
        statements_f: Vec<Vec<Evaluation<EF>>>,
        statements_ef: Vec<Vec<Evaluation<EF>>>,
        log_smallest_decomposition_chunk: usize,
    ) -> Self {
        assert_eq_many!(
            index_columns_f.len(),
            heights_f.len(),
            default_indexes_f.len(),
            value_columns_f.len(),
            statements_f.len()
        );
        assert_eq_many!(
            index_columns_ef.len(),
            heights_ef.len(),
            default_indexes_ef.len(),
            value_columns_ef.len(),
            statements_ef.len()
        );
        let n_cols_f = value_columns_f.len();

        let mut all_value_columns = vec![];
        for col_f in value_columns_f {
            all_value_columns.push(vec![VecOrSlice::Slice(col_f)]);
        }
        for col_ef in &value_columns_ef {
            all_value_columns.push(
                transpose_slice_to_basis_coefficients::<PF<EF>, EF>(col_ef)
                    .into_iter()
                    .map(VecOrSlice::Vec)
                    .collect(),
            );
        }

        let mut multi_eval_statements = vec![];
        for eval_group in &statements_f {
            multi_eval_statements.push(
                eval_group
                    .iter()
                    .map(|e| MultiEvaluation::new(e.point.clone(), vec![e.value]))
                    .collect(),
            );
        }

        for (eval_group, extension_column_split) in
            statements_ef.iter().zip(&all_value_columns[n_cols_f..])
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

        let index_columns = [index_columns_f, index_columns_ef].concat();
        let heights = [heights_f, heights_ef].concat();
        let default_indexes = [default_indexes_f, default_indexes_ef].concat();

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

        Self { generic, n_cols_f }
    }

    // after committing to the pushforward
    pub fn step_2(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        non_zero_memory_size: usize,
    ) -> NormalPackedLookupStatements<EF> {
        let res = self.generic.step_2(prover_state, non_zero_memory_size);
        NormalPackedLookupStatements {
            on_table: res.on_table,
            on_pushforward: res.on_pushforward,
            on_indexes_f: res.on_indexes[..self.n_cols_f].to_vec(),
            on_indexes_ef: res.on_indexes[self.n_cols_f..].to_vec(),
        }
    }
}

#[derive(Debug)]
pub struct NormalPackedLookupVerifier<EF: ExtensionField<PF<EF>>> {
    generic: GenericPackedLookupVerifier<EF>,
    n_cols_f: usize,
}

impl<EF: ExtensionField<PF<EF>>> NormalPackedLookupVerifier<EF>
where
    PF<EF>: PrimeField64,
{
    // before receiving the commitment to the pushforward
    #[allow(clippy::too_many_arguments)]
    pub fn step_1<TF: ExtensionField<PF<EF>>>(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        heights_f: Vec<usize>,
        heights_ef: Vec<usize>,
        default_indexes_f: Vec<usize>,
        default_indexes_ef: Vec<usize>,
        statements_f: Vec<Vec<Evaluation<EF>>>,
        statements_ef: Vec<Vec<Evaluation<EF>>>,
        log_smallest_decomposition_chunk: usize,
        table_initial_values: &[TF],
    ) -> ProofResult<Self>
    where
        EF: ExtensionField<TF>,
    {
        assert_eq_many!(heights_f.len(), default_indexes_f.len(), statements_f.len());
        assert_eq_many!(
            heights_ef.len(),
            default_indexes_ef.len(),
            statements_ef.len()
        );
        let n_cols_f = statements_f.len();

        let mut multi_eval_statements = vec![];
        for eval_group in &statements_f {
            multi_eval_statements.push(
                eval_group
                    .iter()
                    .map(|e| MultiEvaluation::new(e.point.clone(), vec![e.value]))
                    .collect(),
            );
        }
        for eval_group in &statements_ef {
            let mut multi_evals = vec![];
            for eval in eval_group {
                let sub_evals = verifier_state
                    .next_extension_scalars_vec(<EF as BasedVectorSpace<PF<EF>>>::DIMENSION)?;
                if dot_product_with_base(&sub_evals) != eval.value {
                    return Err(ProofError::InvalidProof);
                }
                multi_evals.push(MultiEvaluation::new(eval.point.clone(), sub_evals));
            }

            multi_eval_statements.push(multi_evals);
        }
        let heights = [heights_f, heights_ef].concat();
        let default_indexes = [default_indexes_f, default_indexes_ef].concat();
        let generic = GenericPackedLookupVerifier::step_1(
            verifier_state,
            heights,
            default_indexes,
            multi_eval_statements,
            log_smallest_decomposition_chunk,
            table_initial_values,
        )?;

        Ok(Self { generic, n_cols_f })
    }

    // after receiving the commitment to the pushforward
    pub fn step_2(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        log_memory_size: usize,
    ) -> ProofResult<NormalPackedLookupStatements<EF>> {
        let res = self.generic.step_2(verifier_state, log_memory_size)?;
        Ok(NormalPackedLookupStatements {
            on_table: res.on_table,
            on_pushforward: res.on_pushforward,
            on_indexes_f: res.on_indexes[..self.n_cols_f].to_vec(),
            on_indexes_ef: res.on_indexes[self.n_cols_f..].to_vec(),
        })
    }
}
