use multilinear_toolkit::prelude::*;
use utils::FSProver;
use utils::VecOrSlice;
use utils::assert_eq_many;
use utils::transpose_slice_to_basis_coefficients;

use crate::GenericPackedLookupProver;
use crate::GenericPackedLookupVerifier;

#[derive(Debug)]
pub struct NormalPackedLookupProver;

/// claims contain sparse points (TODO take advantage of it)
#[derive(Debug, PartialEq)]
pub struct NormalPackedLookupStatements<EF, const DIM: usize> {
    pub on_table: Evaluation<EF>,
    pub on_acc: Evaluation<EF>,
    pub on_indexes_f: Vec<Vec<Evaluation<EF>>>,
    pub on_indexes_ef: Vec<Vec<Evaluation<EF>>>,
    pub on_values_f: Vec<Vec<Evaluation<EF>>>,
    pub on_values_ef: Vec<[Vec<Evaluation<EF>>; DIM]>,
}

impl NormalPackedLookupProver {
    #[allow(clippy::too_many_arguments)]
    pub fn run<EF: ExtensionField<PF<EF>>, const DIM: usize>(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        table: &[PF<EF>], // table[0] is assumed to be zero
        acc: &mut [PF<EF>],
        non_zero_memory_size: usize,
        index_columns_f: Vec<&[PF<EF>]>,
        index_columns_ef: Vec<&[PF<EF>]>,
        heights_f: Vec<usize>,
        heights_ef: Vec<usize>,
        default_indexes_f: Vec<usize>,
        default_indexes_ef: Vec<usize>,
        value_columns_f: Vec<&[PF<EF>]>,
        value_columns_ef: Vec<&[EF]>,
        log_smallest_decomposition_chunk: usize,
    ) -> NormalPackedLookupStatements<EF, DIM> {
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

        let index_columns = [index_columns_f, index_columns_ef].concat();
        let heights = [heights_f, heights_ef].concat();
        let default_indexes = [default_indexes_f, default_indexes_ef].concat();

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

        NormalPackedLookupStatements {
            on_table: generic.on_table,
            on_acc: generic.on_acc,
            on_indexes_f: generic.on_indexes[..n_cols_f].to_vec(),
            on_indexes_ef: generic.on_indexes[n_cols_f..].to_vec(),
            on_values_f: generic.on_values[..n_cols_f]
                .iter()
                .map(|e| {
                    assert_eq!(e.len(), 1);
                    e[0].clone()
                })
                .collect(),
            on_values_ef: generic.on_values[n_cols_f..]
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
    pub fn run<EF: ExtensionField<PF<EF>>, const DIM: usize>(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        log_table_len: usize,
        heights_f: Vec<usize>,
        heights_ef: Vec<usize>,
        default_indexes_f: Vec<usize>,
        default_indexes_ef: Vec<usize>,
        log_smallest_decomposition_chunk: usize,
        table_initial_values: &[PF<EF>],
    ) -> ProofResult<NormalPackedLookupStatements<EF, DIM>> {
        assert_eq_many!(heights_f.len(), default_indexes_f.len());
        assert_eq_many!(heights_ef.len(), default_indexes_ef.len());

        let heights = [heights_f.clone(), heights_ef.clone()].concat();
        let default_indexes = [default_indexes_f, default_indexes_ef].concat();
        let n_cols_per_group = [vec![1; heights_f.len()], vec![DIM; heights_ef.len()]].concat();
        let generic = GenericPackedLookupVerifier::run(
            verifier_state,
            log_table_len,
            heights,
            default_indexes,
            n_cols_per_group,
            log_smallest_decomposition_chunk,
            table_initial_values,
        )?;

        Ok(NormalPackedLookupStatements {
            on_table: generic.on_table,
            on_acc: generic.on_acc,
            on_indexes_f: generic.on_indexes[..heights_f.len()].to_vec(),
            on_indexes_ef: generic.on_indexes[heights_f.len()..].to_vec(),
            on_values_f: generic.on_values[..heights_f.len()]
                .iter()
                .map(|e| {
                    assert_eq!(e.len(), 1);
                    e[0].clone()
                })
                .collect(),
            on_values_ef: generic.on_values[heights_f.len()..]
                .iter()
                .map(|e| e.to_vec().try_into().unwrap())
                .collect(),
        })
    }
}
