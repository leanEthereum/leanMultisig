use lookup::compute_pushforward;
use lookup::prove_logup_star;
use lookup::verify_logup_star;
use multilinear_toolkit::prelude::*;
use p3_field::{ExtensionField, Field};
use std::any::TypeId;
use utils::VecOrSlice;
use utils::{FSProver, assert_eq_many};

use crate::{ColDims, MultilinearChunks, packed_pcs_global_statements_for_prover};

#[derive(Debug)]
pub struct GenericPackedLookupProver<'a, TF: Field, EF: ExtensionField<TF> + ExtensionField<PF<EF>>>
{
    // inputs
    pub(crate) table: &'a [TF],
    pub(crate) index_columns: Vec<&'a [PF<EF>]>,

    // outputs
    pub(crate) n_cols_per_group: Vec<usize>,
    pub(crate) chunks: MultilinearChunks,
    pub(crate) packed_lookup_indexes: Vec<PF<EF>>,
    pub(crate) poly_eq_point: Vec<EF>,
    pub(crate) pushforward: Vec<EF>, // to be committed
    pub(crate) batched_value: EF,
}

#[derive(Debug, PartialEq)]
pub struct PackedLookupStatements<EF> {
    pub on_table: Evaluation<EF>,
    pub on_pushforward: Vec<Evaluation<EF>>,
    pub on_indexes: Vec<Vec<Evaluation<EF>>>, // contain sparse points (TODO take advantage of it)
}

impl<'a, TF: Field, EF: ExtensionField<TF> + ExtensionField<PF<EF>>>
    GenericPackedLookupProver<'a, TF, EF>
where
    PF<EF>: PrimeField64,
{
    pub fn pushforward_to_commit(&self) -> &[EF] {
        &self.pushforward
    }

    // before committing to the pushforward
    pub fn step_1(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        table: &'a [TF], // table[0] is assumed to be zero
        index_columns: Vec<&'a [PF<EF>]>,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        value_columns: Vec<Vec<VecOrSlice<'a, TF>>>, // value_columns[i][j] = (index_columns[i] + j)*table (using the notation of https://eprint.iacr.org/2025/946)
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
            .flat_map(|cols| cols.iter().map(|col| col.as_slice()))
            .collect::<Vec<&[TF]>>();

        let mut all_dims = vec![];
        for (i, (default_index, height)) in default_indexes.iter().zip(heights.iter()).enumerate() {
            for col_index in 0..n_cols_per_group[i] {
                all_dims.push(ColDims::padded(*height, table[col_index + default_index]));
            }
        }

        let (_packed_lookup_values, chunks) = crate::compute_multilinear_chunks_and_apply(
            &flatened_value_columns,
            &all_dims,
            log_smallest_decomposition_chunk,
        );

        let packed_statements = packed_pcs_global_statements_for_prover(
            &flatened_value_columns,
            &all_dims,
            log_smallest_decomposition_chunk,
            &expand_multi_evals(&initial_statements),
            prover_state,
        );

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

        let packed_lookup_indexes = chunks.apply(&all_index_cols_ref);

        let batching_scalar = prover_state.sample();

        let mut poly_eq_point = EF::zero_vec(1 << chunks.packed_n_vars);
        for (alpha_power, statement) in batching_scalar.powers().zip(&packed_statements) {
            compute_sparse_eval_eq(&statement.point, &mut poly_eq_point, alpha_power);
        }
        let pushforward = compute_pushforward(&packed_lookup_indexes, table.len(), &poly_eq_point);

        let batched_value: EF = batching_scalar
            .powers()
            .zip(&packed_statements)
            .map(|(alpha_power, statement)| alpha_power * statement.value)
            .sum();

        Self {
            table,
            index_columns,
            n_cols_per_group,
            batched_value,
            packed_lookup_indexes,
            poly_eq_point,
            pushforward,
            chunks,
        }
    }

    // after committing to the pushforward
    pub fn step_2(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        non_zero_memory_size: usize,
    ) -> PackedLookupStatements<EF> {
        let table = if TypeId::of::<TF>() == TypeId::of::<PF<EF>>() {
            MleRef::Base(unsafe { std::mem::transmute::<&[TF], &[PF<EF>]>(self.table) })
        } else if TypeId::of::<TF>() == TypeId::of::<EF>() {
            MleRef::Extension(unsafe { std::mem::transmute::<&[TF], &[EF]>(self.table) })
        } else {
            panic!();
        };
        let logup_star_statements = prove_logup_star(
            prover_state,
            &table,
            &self.packed_lookup_indexes,
            self.batched_value,
            &self.poly_eq_point,
            &self.pushforward,
            Some(non_zero_memory_size),
        );

        let mut value_on_packed_indexes = EF::ZERO;
        let mut offset = 0;
        let mut index_statements_to_prove = vec![];
        for (i, n_cols) in self.n_cols_per_group.iter().enumerate() {
            let my_chunks = &self.chunks[offset..offset + n_cols];
            offset += n_cols;

            assert!(my_chunks.iter().all(|col_chunks| {
                col_chunks.iter().zip(my_chunks[0].iter()).all(|(c1, c2)| {
                    c1.offset_in_original == c2.offset_in_original && c1.n_vars == c2.n_vars
                })
            }));
            let mut inner_statements = vec![];
            let mut inner_evals = vec![];
            for chunk in &my_chunks[0] {
                let sparse_point = MultilinearPoint(
                    [
                        chunk.bits_offset_in_original(),
                        logup_star_statements.on_indexes.point
                            [self.chunks.packed_n_vars - chunk.n_vars..]
                            .to_vec(),
                    ]
                    .concat(),
                );
                let eval = self.index_columns[i].evaluate_sparse(&sparse_point);
                inner_evals.push(eval);
                inner_statements.push(Evaluation::new(sparse_point, eval));
            }
            prover_state.add_extension_scalars(&inner_evals);
            index_statements_to_prove.push(inner_statements);

            for (col_index, chunks_for_col) in my_chunks.iter().enumerate() {
                for (&inner_eval, chunk) in inner_evals.iter().zip(chunks_for_col) {
                    let missing_vars = self.chunks.packed_n_vars - chunk.n_vars;
                    value_on_packed_indexes += (inner_eval + PF::<EF>::from_usize(col_index))
                        * MultilinearPoint(
                            logup_star_statements.on_indexes.point[..missing_vars].to_vec(),
                        )
                        .eq_poly_outside(&MultilinearPoint(
                            chunk.bits_offset_in_packed(self.chunks.packed_n_vars),
                        ));
                }
            }
        }
        // sanity check
        assert_eq!(
            value_on_packed_indexes,
            logup_star_statements.on_indexes.value
        );

        PackedLookupStatements {
            on_table: logup_star_statements.on_table,
            on_pushforward: logup_star_statements.on_pushforward,
            on_indexes: index_statements_to_prove,
        }
    }
}

#[derive(Debug)]
pub struct GenericPackedLookupVerifier<EF: ExtensionField<PF<EF>>> {
    n_cols_per_group: Vec<usize>,
    chunks: MultilinearChunks,
    batching_scalar: EF,
    packed_statements: Vec<Evaluation<EF>>,
}

impl<EF: ExtensionField<PF<EF>>> GenericPackedLookupVerifier<EF>
where
    PF<EF>: PrimeField64,
{
    // before receiving the commitment to the pushforward
    pub fn step_1<TF: ExtensionField<PF<EF>>>(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        initial_statements: Vec<Vec<MultiEvaluation<EF>>>,
        log_smallest_decomposition_chunk: usize,
        table_initial_values: &[TF],
    ) -> ProofResult<Self>
    where
        EF: ExtensionField<TF>,
    {
        let n_cols_per_group = initial_statements
            .iter()
            .map(|evals| evals[0].num_values())
            .collect::<Vec<usize>>();
        let mut all_dims = vec![];
        for (i, (default_index, height)) in default_indexes.iter().zip(heights.iter()).enumerate() {
            for col_index in 0..n_cols_per_group[i] {
                all_dims.push(ColDims::padded(
                    *height,
                    table_initial_values[col_index + default_index],
                ));
            }
        }

        let packed_statements = crate::packed_pcs_global_statements_for_verifier(
            &all_dims,
            log_smallest_decomposition_chunk,
            &expand_multi_evals(&initial_statements),
            verifier_state,
            &Default::default(),
        )?;
        let chunks = MultilinearChunks::compute(&all_dims, log_smallest_decomposition_chunk);

        let batching_scalar = verifier_state.sample();

        Ok(Self {
            n_cols_per_group,
            chunks,
            batching_scalar,
            packed_statements,
        })
    }

    // after receiving the commitment to the pushforward
    pub fn step_2(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        log_memory_size: usize,
    ) -> ProofResult<PackedLookupStatements<EF>> {
        let logup_star_statements = verify_logup_star(
            verifier_state,
            log_memory_size,
            self.chunks.packed_n_vars,
            &self.packed_statements,
            self.batching_scalar,
        )
        .unwrap();

        let mut value_on_packed_indexes = EF::ZERO;
        let mut offset = 0;
        let mut index_statements_to_verify = vec![];
        for n_cols in &self.n_cols_per_group {
            let my_chunks = &self.chunks[offset..offset + n_cols];
            offset += n_cols;

            // sanity check
            assert!(my_chunks.iter().all(|col_chunks| {
                col_chunks.iter().zip(my_chunks[0].iter()).all(|(c1, c2)| {
                    c1.offset_in_original == c2.offset_in_original && c1.n_vars == c2.n_vars
                })
            }));
            let mut inner_statements = vec![];
            let inner_evals = verifier_state.next_extension_scalars_vec(my_chunks[0].len())?;
            for (chunk, &eval) in my_chunks[0].iter().zip(&inner_evals) {
                let sparse_point = MultilinearPoint(
                    [
                        chunk.bits_offset_in_original(),
                        logup_star_statements.on_indexes.point
                            [self.chunks.packed_n_vars - chunk.n_vars..]
                            .to_vec(),
                    ]
                    .concat(),
                );
                inner_statements.push(Evaluation::new(sparse_point, eval));
            }
            index_statements_to_verify.push(inner_statements);

            for (col_index, chunks_for_col) in my_chunks.iter().enumerate() {
                for (&inner_eval, chunk) in inner_evals.iter().zip(chunks_for_col) {
                    let missing_vars = self.chunks.packed_n_vars - chunk.n_vars;
                    value_on_packed_indexes += (inner_eval + PF::<EF>::from_usize(col_index))
                        * MultilinearPoint(
                            logup_star_statements.on_indexes.point[..missing_vars].to_vec(),
                        )
                        .eq_poly_outside(&MultilinearPoint(
                            chunk.bits_offset_in_packed(self.chunks.packed_n_vars),
                        ));
                }
            }
        }
        if value_on_packed_indexes != logup_star_statements.on_indexes.value {
            return Err(ProofError::InvalidProof);
        }

        Ok(PackedLookupStatements {
            on_table: logup_star_statements.on_table,
            on_pushforward: logup_star_statements.on_pushforward,
            on_indexes: index_statements_to_verify,
        })
    }
}

fn expand_multi_evals<EF: Field>(
    statements: &[Vec<MultiEvaluation<EF>>],
) -> Vec<Vec<Evaluation<EF>>> {
    statements
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
        .collect::<Vec<_>>()
}
