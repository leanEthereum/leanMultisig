use multilinear_toolkit::prelude::*;
use p3_field::{ExtensionField, Field};
use utils::{FSProver, assert_eq_many};

use crate::{ColDims, MultilinearChunks, packed_pcs_global_statements_for_prover};

#[derive(Debug)]
pub struct PackedLookupProver<'a, F: Field, EF: ExtensionField<F>> {
    pub table: &'a [EF],
    pub index_columns: Vec<&'a [F]>,
    pub heights: Vec<usize>,
    pub default_indexes: Vec<usize>,
    pub value_columns: Vec<Vec<&'a [EF]>>, // value_columns[i][j] = (index_columns[i] + j)*table (using the notation of https://eprint.iacr.org/2025/946)
    pub initial_statements: Vec<MultilinearPoint<EF>>,

    pub chunks: MultilinearChunks,
    pub pushforward: Vec<EF>,
}

impl<'a, F: Field, EF: ExtensionField<F> + ExtensionField<PF<EF>>> PackedLookupProver<'a, F, EF> {
    pub fn new(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        table: &'a [EF],
        index_columns: Vec<&'a [F]>,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        value_columns: Vec<Vec<&'a [EF]>>,
        initial_statements: Vec<Vec<MultiEvaluation<EF>>>,
        log_smallest_decomposition_chunk: usize,
    ) -> Self {
        assert!(table[0].is_zero());
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

        let flatened_value_columns = value_columns
            .iter()
            .flat_map(|cols| cols.iter().map(|col| *col))
            .collect::<Vec<&[EF]>>();

        let mut all_dims = vec![];
        for (default_index, (height, values)) in default_indexes
            .iter()
            .zip(heights.iter().zip(value_columns.iter()))
        {
            let n_cols = values.len();
            for col_index in 0..n_cols {
                all_dims.push(ColDims::padded(*height, table[col_index + default_index]));
            }
        }

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

        todo!()
    }
}
