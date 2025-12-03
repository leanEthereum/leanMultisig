use lookup::prove_logup;
use lookup::verify_logup;
use multilinear_toolkit::prelude::*;
use utils::to_big_endian_in_field;
use utils::{FSProver, assert_eq_many};

use crate::{ColDims, MultilinearChunks};

#[derive(Debug)]
pub struct GenericPackedLookupProver;

#[derive(Debug, PartialEq)]
pub struct PackedLookupStatements<EF> {
    pub on_table: Evaluation<EF>,
    pub on_acc: Evaluation<EF>,
    pub on_indexes: Vec<Vec<Evaluation<EF>>>, // contain sparse points (TODO take advantage of it)
    pub on_values: Vec<Vec<Vec<Evaluation<EF>>>>, // contain sparse points (TODO take advantage of it)
}

fn tweak_acc_vector<EF: ExtensionField<PF<EF>>>(
    at_start: bool,
    acc: &mut Vec<PF<EF>>,
    index_columns: &Vec<&[PF<EF>]>,
    n_cols_per_group: &Vec<usize>,
    default_indexes: &Vec<usize>,
    chunks: &MultilinearChunks,
) {
    let selector = if at_start { PF::<EF>::ONE } else { PF::<EF>::NEG_ONE };
    let mut total_size = 0;
    let mut offset = 0;
    for (i, n_cols) in n_cols_per_group.iter().enumerate() {
        let my_chunks = &chunks[offset..offset + n_cols];
        offset += n_cols;
        let full_height = index_columns[i].len();
        assert!(full_height.is_power_of_two());
        for j in 0..*n_cols {
            total_size += full_height;
            let chunk_height = my_chunks[j].iter().map(|c| 1 << c.n_vars).sum();
            let default_index = default_indexes[i] + j;
            let height_diff = PF::<EF>::from_usize(full_height.checked_sub(chunk_height).unwrap());
            acc[default_index] -= height_diff * selector;
            acc[0] += height_diff * selector;
        }
    }
    let global_height_diff = PF::<EF>::from_usize(1usize << chunks.packed_n_vars) - PF::<EF>::from_usize(total_size);
    acc[0] += global_height_diff * selector;
}

fn tweak_acc_statement<EF: ExtensionField<PF<EF>>>(
    acc_statement: &mut Evaluation<EF>,
    n_cols_per_group: &Vec<usize>,
    heights: &Vec<usize>,
    default_indexes: &Vec<usize>,
    chunks: &MultilinearChunks,
    log_table_len: usize,
) {
    let mut offset = 0;
    let mut total_size = 0;
    for (i, n_cols) in n_cols_per_group.iter().enumerate() {
        let my_chunks = &chunks[offset..offset + n_cols];
        offset += n_cols;
        let full_height = heights[i].next_power_of_two();
        for j in 0..*n_cols {
            total_size += full_height;
            let chunk_height = my_chunks[j].iter().map(|c| 1 << c.n_vars).sum();
            let default_index = default_indexes[i] + j;
            let height_diff = PF::<EF>::from_usize(full_height.checked_sub(chunk_height).unwrap());

            acc_statement.value += MultilinearPoint(to_big_endian_in_field(default_index, log_table_len))
                .eq_poly_outside(&acc_statement.point)
                * height_diff;
            acc_statement.value -= MultilinearPoint(to_big_endian_in_field(0, log_table_len))
                .eq_poly_outside(&acc_statement.point)
                * height_diff;
        }
    }
    let global_height_diff = PF::<EF>::from_usize(1usize << chunks.packed_n_vars) - PF::<EF>::from_usize(total_size);
    acc_statement.value -= MultilinearPoint(to_big_endian_in_field(0, log_table_len))
        .eq_poly_outside(&acc_statement.point)
        * global_height_diff;
}

impl GenericPackedLookupProver {
    #[allow(clippy::too_many_arguments)]
    pub fn run<'a, EF: ExtensionField<PF<EF>>>(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        table: &'a [PF<EF>], // table[0] is assumed to be zero
        acc: &mut Vec<PF<EF>>,
        index_columns: Vec<&'a [PF<EF>]>,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        value_columns: Vec<Vec<&'a [PF<EF>]>>, // value_columns[i][j] = (index_columns[i] + j)*table (using the notation of https://eprint.iacr.org/2025/946)
        log_smallest_decomposition_chunk: usize,
        non_zero_memory_size: usize,
    ) -> PackedLookupStatements<EF> {
        assert!(table[0].is_zero());
        assert!(table.len().is_power_of_two());
        assert_eq_many!(
            index_columns.len(),
            heights.len(),
            default_indexes.len(),
            value_columns.len(),
        );
        let n_groups = value_columns.len();
        let n_cols_per_group = value_columns.iter().map(|cols| cols.len()).collect::<Vec<usize>>();

        let flatened_value_columns = value_columns
            .iter()
            .flat_map(|cols| cols.iter().map(|col| &col[..]))
            .collect::<Vec<&[PF<EF>]>>();

        let mut all_dims = vec![];
        for (i, (default_index, height)) in default_indexes.iter().zip(heights.iter()).enumerate() {
            for col_index in 0..n_cols_per_group[i] {
                all_dims.push(ColDims::padded(*height, table[col_index + default_index]));
            }
        }

        let (concatenated_values, chunks) = crate::compute_multilinear_chunks_and_apply(
            &flatened_value_columns,
            &all_dims,
            log_smallest_decomposition_chunk,
        );

        tweak_acc_vector::<EF>(true, acc, &index_columns, &n_cols_per_group, &default_indexes, &chunks);

        let mut missing_shifted_index_cols = vec![vec![]; n_groups];
        for (i, index_col) in index_columns.iter().enumerate() {
            for j in 1..n_cols_per_group[i] {
                let shifted_col = index_col
                    .par_iter()
                    .map(|&x| x + PF::<EF>::from_usize(j))
                    .collect::<Vec<PF<EF>>>();
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

        let concatenated_indexes = chunks.apply(&all_index_cols_ref);

        let mut logup_statements = prove_logup(
            prover_state,
            &concatenated_indexes,
            &concatenated_values,
            &table,
            &acc,
            Some(non_zero_memory_size),
        );

        let mut eval_concatenated_indexes = EF::ZERO;
        let mut eval_concatenated_values = EF::ZERO;
        let mut offset = 0;
        let mut index_statements_to_prove = vec![];
        let mut value_statements_to_prove = vec![];
        for (index_col, value_cols) in index_columns.iter().zip(&value_columns) {
            let n_cols = value_cols.len();
            let my_chunks = &chunks[offset..offset + n_cols];
            offset += n_cols;

            assert!(my_chunks.iter().all(|col_chunks| {
                col_chunks
                    .iter()
                    .zip(my_chunks[0].iter())
                    .all(|(c1, c2)| c1.offset_in_original == c2.offset_in_original && c1.n_vars == c2.n_vars)
            }));

            {
                // Indexes

                let mut inner_statements = vec![];
                let mut inner_evals = vec![];
                for chunk in &my_chunks[0] {
                    let sparse_point = MultilinearPoint(
                        [
                            chunk.bits_offset_in_original(),
                            logup_statements.on_indexes.point[chunks.packed_n_vars - chunk.n_vars..].to_vec(),
                        ]
                        .concat(),
                    );
                    let eval = index_col.evaluate_sparse(&sparse_point);
                    inner_evals.push(eval);
                    inner_statements.push(Evaluation::new(sparse_point, eval));
                }
                prover_state.add_extension_scalars(&inner_evals);
                index_statements_to_prove.push(inner_statements);

                for (col_index, chunks_for_col) in my_chunks.iter().enumerate() {
                    for (&inner_eval, chunk) in inner_evals.iter().zip(chunks_for_col) {
                        let missing_vars = chunks.packed_n_vars - chunk.n_vars;
                        eval_concatenated_indexes += (inner_eval + PF::<EF>::from_usize(col_index))
                            * MultilinearPoint(logup_statements.on_indexes.point[..missing_vars].to_vec())
                                .eq_poly_outside(&MultilinearPoint(chunk.bits_offset_in_packed(chunks.packed_n_vars)));
                    }
                }
            }

            {
                // Values
                let mut all_inner_statements = vec![];
                for (col_chunks, value_col) in my_chunks.iter().zip(value_cols.iter()) {
                    let mut inner_statements = vec![];
                    let mut inner_evals = vec![];
                    for chunk in col_chunks {
                        let sparse_point = MultilinearPoint(
                            [
                                chunk.bits_offset_in_original(),
                                logup_statements.on_values.point[chunks.packed_n_vars - chunk.n_vars..].to_vec(),
                            ]
                            .concat(),
                        );
                        let eval = value_col.evaluate_sparse(&sparse_point);

                        let missing_vars = chunks.packed_n_vars - chunk.n_vars;
                        eval_concatenated_values += eval
                            * MultilinearPoint(logup_statements.on_values.point[..missing_vars].to_vec())
                                .eq_poly_outside(&MultilinearPoint(chunk.bits_offset_in_packed(chunks.packed_n_vars)));

                        inner_evals.push(eval);
                        inner_statements.push(Evaluation::new(sparse_point, eval));
                    }
                    prover_state.add_extension_scalars(&inner_evals);
                    all_inner_statements.push(inner_statements);
                }
                value_statements_to_prove.push(all_inner_statements);
            }
        }
        // sanity check
        assert_eq!(eval_concatenated_indexes, logup_statements.on_indexes.value);
        assert_eq!(eval_concatenated_values, logup_statements.on_values.value);

        tweak_acc_statement::<EF>(
            &mut logup_statements.on_acc,
            &n_cols_per_group,
            &heights,
            &default_indexes,
            &chunks,
            log2_ceil_usize(table.len()),
        );
        tweak_acc_vector::<EF>(false, acc, &index_columns, &n_cols_per_group, &default_indexes, &chunks);

        PackedLookupStatements {
            on_table: logup_statements.on_table,
            on_acc: logup_statements.on_acc,
            on_indexes: index_statements_to_prove,
            on_values: value_statements_to_prove,
        }
    }
}

#[derive(Debug)]
pub struct GenericPackedLookupVerifier;

impl GenericPackedLookupVerifier {
    pub fn run<EF: ExtensionField<PF<EF>>>(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        log_table_len: usize,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        n_cols_per_group: Vec<usize>,
        log_smallest_decomposition_chunk: usize,
        table_initial_values: &[PF<EF>],
    ) -> ProofResult<PackedLookupStatements<EF>> {
        let mut all_dims = vec![];
        for (i, (default_index, height)) in default_indexes.iter().zip(heights.iter()).enumerate() {
            for col_index in 0..n_cols_per_group[i] {
                all_dims.push(ColDims::padded(
                    *height,
                    table_initial_values[col_index + default_index],
                ));
            }
        }

        let chunks = MultilinearChunks::compute(&all_dims, log_smallest_decomposition_chunk);

        let mut logup_statements = verify_logup(verifier_state, log_table_len, chunks.packed_n_vars)?;

        let mut eval_concatenated_indexes = EF::ZERO;
        let mut eval_concatenated_values = EF::ZERO;
        let mut offset = 0;
        let mut index_statements_to_verify = vec![];
        let mut value_statements_to_verify = vec![];
        for n_cols in &n_cols_per_group {
            let my_chunks = &chunks[offset..offset + n_cols];
            offset += n_cols;

            // sanity check
            assert!(my_chunks.iter().all(|col_chunks| {
                col_chunks
                    .iter()
                    .zip(my_chunks[0].iter())
                    .all(|(c1, c2)| c1.offset_in_original == c2.offset_in_original && c1.n_vars == c2.n_vars)
            }));

            {
                // Indexes
                let mut inner_statements = vec![];
                let inner_evals = verifier_state.next_extension_scalars_vec(my_chunks[0].len())?;
                for (chunk, &eval) in my_chunks[0].iter().zip(&inner_evals) {
                    let sparse_point = MultilinearPoint(
                        [
                            chunk.bits_offset_in_original(),
                            logup_statements.on_indexes.point[chunks.packed_n_vars - chunk.n_vars..].to_vec(),
                        ]
                        .concat(),
                    );
                    inner_statements.push(Evaluation::new(sparse_point, eval));
                }
                index_statements_to_verify.push(inner_statements);

                for (col_index, chunks_for_col) in my_chunks.iter().enumerate() {
                    for (&inner_eval, chunk) in inner_evals.iter().zip(chunks_for_col) {
                        let missing_vars = chunks.packed_n_vars - chunk.n_vars;
                        eval_concatenated_indexes += (inner_eval + PF::<EF>::from_usize(col_index))
                            * MultilinearPoint(logup_statements.on_indexes.point[..missing_vars].to_vec())
                                .eq_poly_outside(&MultilinearPoint(chunk.bits_offset_in_packed(chunks.packed_n_vars)));
                    }
                }
            }

            {
                // Values

                let mut all_inner_statements = vec![];
                for col_chunks in my_chunks {
                    let mut inner_statements = vec![];
                    let inner_evals = verifier_state.next_extension_scalars_vec(col_chunks.len())?;
                    for (chunk, &eval) in col_chunks.iter().zip(&inner_evals) {
                        let sparse_point = MultilinearPoint(
                            [
                                chunk.bits_offset_in_original(),
                                logup_statements.on_indexes.point[chunks.packed_n_vars - chunk.n_vars..].to_vec(),
                            ]
                            .concat(),
                        );
                        inner_statements.push(Evaluation::new(sparse_point, eval));
                        let missing_vars = chunks.packed_n_vars - chunk.n_vars;
                        eval_concatenated_values += eval
                            * MultilinearPoint(logup_statements.on_indexes.point[..missing_vars].to_vec())
                                .eq_poly_outside(&MultilinearPoint(chunk.bits_offset_in_packed(chunks.packed_n_vars)));
                    }
                    all_inner_statements.push(inner_statements);
                }
                value_statements_to_verify.push(all_inner_statements);
            }
        }
        if eval_concatenated_values != logup_statements.on_values.value {
            return Err(ProofError::InvalidProof);
        }
        if eval_concatenated_indexes != logup_statements.on_indexes.value {
            return Err(ProofError::InvalidProof);
        }

        tweak_acc_statement::<EF>(
            &mut logup_statements.on_acc,
            &n_cols_per_group,
            &heights,
            &default_indexes,
            &chunks,
            log_table_len,
        );

        Ok(PackedLookupStatements {
            on_table: logup_statements.on_table,
            on_acc: logup_statements.on_acc,
            on_indexes: index_statements_to_verify,
            on_values: value_statements_to_verify,
        })
    }
}
