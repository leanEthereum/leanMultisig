use lookup::compute_pushforward;
use multilinear_toolkit::prelude::*;
use p3_field::{ExtensionField, Field};
use utils::{FSProver, assert_eq_many};

use crate::{ColDims, MultilinearChunks, packed_pcs_global_statements_for_prover};

#[derive(Debug)]
pub struct PackedLookupProver<'a, F: Field, EF: ExtensionField<F>> {
    // inputs
    pub table: &'a [EF],
    pub index_columns: Vec<&'a [F]>,
    pub heights: Vec<usize>,
    pub default_indexes: Vec<usize>,
    pub value_columns: Vec<Vec<&'a [EF]>>, // value_columns[i][j] = (index_columns[i] + j)*table (using the notation of https://eprint.iacr.org/2025/946)
    pub initial_statements: Vec<Vec<MultiEvaluation<EF>>>,

    // outputs
    pub chunks: MultilinearChunks,
    pub pushforward: Vec<EF>, // to be committed
    pub batching_scalar: EF,
    pub batched_value: EF,
}

impl<'a, F: PrimeField64, EF: ExtensionField<F> + ExtensionField<PF<EF>>>
    PackedLookupProver<'a, F, EF>
{
    pub fn step_1(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        table: &'a [EF], // table[0] is assumed to be zero
        index_columns: Vec<&'a [F]>,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        value_columns: Vec<Vec<&'a [EF]>>,
        initial_statements: Vec<Vec<MultiEvaluation<EF>>>,
        log_smallest_decomposition_chunk: usize,
    ) -> Self {
        assert!(table[0].is_zero());
        assert!(table.len().is_power_of_two());
        assert_eq_many!(
            index_columns.len(),
            heights.len(),
            default_indexes.len(),
            value_columns.len(),
            initial_statements.len()
        );
        value_columns
            .iter()
            .zip(&initial_statements)
            .for_each(|(cols, evals)| {
                assert_eq!(cols.len(), evals[0].num_values());
            });
        let n_groups = value_columns.len();
        let n_cols_per_group = value_columns
            .iter()
            .map(|cols| cols.len())
            .collect::<Vec<usize>>();

        let flatened_value_columns = value_columns
            .iter()
            .flat_map(|cols| cols.iter().map(|col| *col))
            .collect::<Vec<&[EF]>>();

        let mut all_dims = vec![];
        for (i, (default_index, height)) in default_indexes.iter().zip(heights.iter()).enumerate() {
            for col_index in 0..n_cols_per_group[i] {
                all_dims.push(ColDims::padded(*height, table[col_index + default_index]));
            }
        }

        let (packed_lookup_values, chunks) = crate::compute_multilinear_chunks_and_apply(
            &flatened_value_columns,
            &all_dims,
            log_smallest_decomposition_chunk,
        );

        let packed_statements = packed_pcs_global_statements_for_prover(
            &flatened_value_columns,
            &all_dims,
            log_smallest_decomposition_chunk,
            &initial_statements
                .iter()
                .map(|multi_evals| {
                    let mut evals = vec![vec![]; multi_evals[0].num_values()];
                    for meval in multi_evals {
                        for (i, &v) in meval.values.iter().enumerate() {
                            evals[i].push(Evaluation::new(meval.point.clone(), v));
                        }
                    }
                    evals
                })
                .flatten()
                .collect::<Vec<_>>(),
            prover_state,
        );

        let mut missing_shifted_index_cols = vec![vec![]; n_groups];
        for (i, index_col) in index_columns.iter().enumerate() {
            for j in 1..n_cols_per_group[i] {
                let shifted_col = index_col
                    .par_iter()
                    .map(|&x| x + F::from_usize(j))
                    .collect::<Vec<F>>();
                missing_shifted_index_cols[i].push(shifted_col);
            }
        }
        let mut all_index_cols_ref = vec![];
        for (i, index_col) in index_columns.iter().enumerate() {
            all_index_cols_ref.push(*index_col);
            for shifted_col in &missing_shifted_index_cols[i] {
                all_index_cols_ref.push(shifted_col.as_slice());
            }
        }

        let packed_lookup_indexes = chunks.apply(&all_index_cols_ref);

        let batching_scalar = prover_state.sample();

        let mut poly_eq_point = EF::zero_vec(1 << chunks.packed_n_vars);
        for (alpha_power, statement) in batching_scalar.powers().zip(&packed_statements) {
            compute_sparse_eval_eq(&statement.point, &mut poly_eq_point, alpha_power);
        }
        let pushforward = compute_pushforward(
            &packed_lookup_indexes,
            log2_strict_usize(table.len()),
            &poly_eq_point,
        );

        let batched_value: EF = batching_scalar
            .powers()
            .zip(&packed_statements)
            .map(|(alpha_power, statement)| alpha_power * statement.value)
            .sum();

        Self {
            table,
            index_columns,
            heights,
            default_indexes,
            value_columns,
            batching_scalar,
            batched_value,
            pushforward,
            initial_statements,
            chunks,
        }
    }
}
