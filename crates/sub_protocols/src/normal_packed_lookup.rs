use multilinear_toolkit::prelude::*;
use utils::FSProver;
use utils::VecOrSlice;
use utils::assert_eq_many;
use utils::collect_refs;
use utils::transpose_slice_to_basis_coefficients;

use crate::GenericPackedLookupProver;
use crate::GenericPackedLookupVerifier;

#[derive(Debug)]
pub struct NormalPackedLookupProver;

/// claims contain sparse points (TODO take advantage of it)
#[derive(Debug, PartialEq)]
pub struct NormalPackedLookupStatements<EF, const DIM: usize, const VECTOR_LEN: usize> {
    pub on_table: Evaluation<EF>,
    pub on_acc: Evaluation<EF>,
    pub on_indexes_f: Vec<Vec<Evaluation<EF>>>,
    pub on_indexes_ef: Vec<Vec<Evaluation<EF>>>,
    pub on_indexes_vec: Vec<Vec<Evaluation<EF>>>,
    pub on_values_f: Vec<Vec<Evaluation<EF>>>,
    pub on_values_ef: Vec<[Vec<Evaluation<EF>>; DIM]>,
    pub on_values_vec: Vec<[Vec<Evaluation<EF>>; VECTOR_LEN]>,
}

impl NormalPackedLookupProver {
    #[allow(clippy::too_many_arguments)]
    pub fn run<EF: ExtensionField<PF<EF>>, const DIM: usize, const VECTOR_LEN: usize>(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        table: &[PF<EF>], // table[0] is assumed to be zero
        acc: &mut [PF<EF>],
        non_zero_memory_size: usize,
        index_columns_f: Vec<&[PF<EF>]>,
        index_columns_ef: Vec<&[PF<EF>]>,
        index_columns_vec: Vec<&[PF<EF>]>,
        heights_f: Vec<usize>,
        heights_ef: Vec<usize>,
        heights_vec: Vec<usize>,
        default_indexes_f: Vec<usize>,
        default_indexes_ef: Vec<usize>,
        default_indexes_vec: Vec<usize>,
        value_columns_f: Vec<&[PF<EF>]>,
        value_columns_ef: Vec<&[EF]>,
        value_columns_vec: Vec<[&[PF<EF>]; VECTOR_LEN]>,
        log_smallest_decomposition_chunk: usize,
    ) -> NormalPackedLookupStatements<EF, DIM, VECTOR_LEN> {
        assert_eq_many!(
            index_columns_f.len(),
            heights_f.len(),
            default_indexes_f.len(),
            value_columns_f.len(),
        );
        assert_eq_many!(
            index_columns_ef.len(),
            heights_ef.len(),
            default_indexes_ef.len(),
            value_columns_ef.len(),
        );
        assert_eq_many!(
            index_columns_vec.len(),
            heights_vec.len(),
            default_indexes_vec.len(),
            value_columns_vec.len(),
        );
        let n_cols_f = value_columns_f.len();
        let n_cols_ef = value_columns_ef.len();

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
        for col_vec in &value_columns_vec {
            all_value_columns.push(col_vec.iter().map(|s| VecOrSlice::Slice(s)).collect());
        }

        // TODO remove
        let index_columns_vec = index_columns_vec
            .par_iter()
            .map(|col| {
                col.par_iter()
                    .map(|&v| v * PF::<EF>::from_usize(VECTOR_LEN))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let default_indexes_vec = default_indexes_vec
            .iter()
            .map(|&idx| idx * VECTOR_LEN)
            .collect::<Vec<_>>();

        let index_columns = [index_columns_f, index_columns_ef, collect_refs(&index_columns_vec)].concat();
        let heights = [heights_f, heights_ef, heights_vec].concat();
        let default_indexes = [default_indexes_f, default_indexes_ef, default_indexes_vec].concat();

        let generic = GenericPackedLookupProver::run(
            prover_state,
            table,
            acc,
            index_columns,
            heights,
            default_indexes,
            all_value_columns,
            log_smallest_decomposition_chunk,
            non_zero_memory_size,
        );

        let mut on_indexes_vec = generic.on_indexes[n_cols_f + n_cols_ef..].to_vec();
        let inv_vector_len = PF::<EF>::from_usize(VECTOR_LEN).inverse();
        for statements in &mut on_indexes_vec {
            for statement in statements {
                statement.value *= inv_vector_len;
            }
        }

        NormalPackedLookupStatements {
            on_table: generic.on_table,
            on_acc: generic.on_acc,
            on_indexes_f: generic.on_indexes[..n_cols_f].to_vec(),
            on_indexes_ef: generic.on_indexes[n_cols_f..][..n_cols_ef].to_vec(),
            on_indexes_vec,
            on_values_f: generic.on_values[..n_cols_f]
                .iter()
                .map(|e| {
                    assert_eq!(e.len(), 1);
                    e[0].clone()
                })
                .collect(),
            on_values_ef: generic.on_values[n_cols_f..][..n_cols_ef]
                .iter()
                .map(|e| e.to_vec().try_into().unwrap())
                .collect(),
            on_values_vec: generic.on_values[n_cols_f + n_cols_ef..]
                .iter()
                .map(|e| e.to_vec().try_into().unwrap())
                .collect(),
        }
    }
}

#[derive(Debug)]
pub struct NormalPackedLookupVerifier;

impl NormalPackedLookupVerifier {
    #[allow(clippy::too_many_arguments)]
    pub fn run<EF: ExtensionField<PF<EF>>, const DIM: usize, const VECTOR_LEN: usize>(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        log_table_len: usize,
        heights_f: Vec<usize>,
        heights_ef: Vec<usize>,
        heights_vec: Vec<usize>,
        default_indexes_f: Vec<usize>,
        default_indexes_ef: Vec<usize>,
        default_indexes_vec: Vec<usize>,
        log_smallest_decomposition_chunk: usize,
        table_initial_values: &[PF<EF>],
    ) -> ProofResult<NormalPackedLookupStatements<EF, DIM, VECTOR_LEN>> {
        assert_eq_many!(heights_f.len(), default_indexes_f.len());
        assert_eq_many!(heights_ef.len(), default_indexes_ef.len());
        assert_eq_many!(heights_vec.len(), default_indexes_vec.len());

        let default_indexes_vec = default_indexes_vec
            .iter()
            .map(|&idx| idx * VECTOR_LEN)
            .collect::<Vec<_>>();

        let heights = [heights_f.clone(), heights_ef.clone(), heights_vec.clone()].concat();
        let default_indexes = [default_indexes_f, default_indexes_ef, default_indexes_vec].concat();
        let n_cols_per_group = [
            vec![1; heights_f.len()],
            vec![DIM; heights_ef.len()],
            vec![VECTOR_LEN; heights_vec.len()],
        ]
        .concat();
        let generic = GenericPackedLookupVerifier::run(
            verifier_state,
            log_table_len,
            heights,
            default_indexes,
            n_cols_per_group,
            log_smallest_decomposition_chunk,
            table_initial_values,
        )?;

        let mut on_indexes_vec = generic.on_indexes[heights_f.len() + heights_ef.len()..].to_vec();
        let inv_vector_len = PF::<EF>::from_usize(VECTOR_LEN).inverse();
        for statements in &mut on_indexes_vec {
            for statement in statements {
                statement.value *= inv_vector_len;
            }
        }

        Ok(NormalPackedLookupStatements {
            on_table: generic.on_table,
            on_acc: generic.on_acc,
            on_indexes_f: generic.on_indexes[..heights_f.len()].to_vec(),
            on_indexes_ef: generic.on_indexes[heights_f.len()..][..heights_ef.len()].to_vec(),
            on_indexes_vec,
            on_values_f: generic.on_values[..heights_f.len()]
                .iter()
                .map(|e| {
                    assert_eq!(e.len(), 1);
                    e[0].clone()
                })
                .collect(),
            on_values_ef: generic.on_values[heights_f.len()..][..heights_ef.len()]
                .iter()
                .map(|e| e.to_vec().try_into().unwrap())
                .collect(),
            on_values_vec: generic.on_values[heights_f.len() + heights_ef.len()..]
                .iter()
                .map(|e| e.to_vec().try_into().unwrap())
                .collect(),
        })
    }
}
