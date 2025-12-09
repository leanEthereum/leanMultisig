use multilinear_toolkit::prelude::*;
use utils::FSProver;
use utils::VecOrSlice;
use utils::collect_refs;
use utils::transpose_slice_to_basis_coefficients;

use crate::{GeneralizedLogupProver, GeneralizedLogupVerifier};

#[derive(Debug)]
pub struct CustomPackedLookupProver;

/// claims contain sparse points (TODO take advantage of it)
#[derive(Debug, PartialEq)]
pub struct CustomPackedLookupStatements<EF, const DIM: usize, const VECTOR_LEN: usize> {
    pub on_table: Evaluation<EF>,
    pub on_acc: Evaluation<EF>,
    pub on_indexes_f: Vec<Evaluation<EF>>,
    pub on_indexes_ef: Vec<Evaluation<EF>>,
    pub on_indexes_vec: Vec<Evaluation<EF>>,
    pub on_values_f: Vec<Evaluation<EF>>,
    pub on_values_ef: Vec<[Evaluation<EF>; DIM]>,
    pub on_values_vec: Vec<[Evaluation<EF>; VECTOR_LEN]>,
}

impl CustomPackedLookupProver {
    #[allow(clippy::too_many_arguments)]
    pub fn run<EF: ExtensionField<PF<EF>>, const DIM: usize, const VECTOR_LEN: usize>(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        table: &[PF<EF>], // table[0] is assumed to be zero
        acc: &[PF<EF>],
        index_columns_f: Vec<&[PF<EF>]>,
        index_columns_ef: Vec<&[PF<EF>]>,
        index_columns_vec: Vec<&[PF<EF>]>,
        value_columns_f: Vec<&[PF<EF>]>,
        value_columns_ef: Vec<&[EF]>,
        value_columns_vec: Vec<[&[PF<EF>]; VECTOR_LEN]>,
    ) -> CustomPackedLookupStatements<EF, DIM, VECTOR_LEN> {
        assert_eq!(index_columns_f.len(), value_columns_f.len(),);
        assert_eq!(index_columns_ef.len(), value_columns_ef.len(),);
        assert_eq!(index_columns_vec.len(), value_columns_vec.len(),);
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

        let index_columns = [index_columns_f, index_columns_ef, collect_refs(&index_columns_vec)].concat();

        let generic = GeneralizedLogupProver::run(prover_state, table, acc, index_columns, all_value_columns);

        let mut on_indexes_vec = generic.on_indexes[n_cols_f + n_cols_ef..].to_vec();
        let inv_vector_len = PF::<EF>::from_usize(VECTOR_LEN).inverse();
        for statement in &mut on_indexes_vec {
            statement.value *= inv_vector_len;
        }

        CustomPackedLookupStatements {
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
        table_log_len: usize,
        log_heights_f: Vec<usize>,
        log_heights_ef: Vec<usize>,
        log_heights_vec: Vec<usize>,
    ) -> ProofResult<CustomPackedLookupStatements<EF, DIM, VECTOR_LEN>> {
        let log_heights = [log_heights_f.clone(), log_heights_ef.clone(), log_heights_vec.clone()].concat();
        let n_cols_per_group = [
            vec![1; log_heights_f.len()],
            vec![DIM; log_heights_ef.len()],
            vec![VECTOR_LEN; log_heights_vec.len()],
        ]
        .concat();
        let generic = GeneralizedLogupVerifier::run(verifier_state, table_log_len, log_heights, n_cols_per_group)?;

        let mut on_indexes_vec = generic.on_indexes[log_heights_f.len() + log_heights_ef.len()..].to_vec();
        let inv_vector_len = PF::<EF>::from_usize(VECTOR_LEN).inverse();
        for statement in &mut on_indexes_vec {
            statement.value *= inv_vector_len;
        }

        Ok(CustomPackedLookupStatements {
            on_table: generic.on_table,
            on_acc: generic.on_acc,
            on_indexes_f: generic.on_indexes[..log_heights_f.len()].to_vec(),
            on_indexes_ef: generic.on_indexes[log_heights_f.len()..][..log_heights_ef.len()].to_vec(),
            on_indexes_vec,
            on_values_f: generic.on_values[..log_heights_f.len()]
                .iter()
                .map(|e| {
                    assert_eq!(e.len(), 1);
                    e[0].clone()
                })
                .collect(),
            on_values_ef: generic.on_values[log_heights_f.len()..][..log_heights_ef.len()]
                .iter()
                .map(|e| e.to_vec().try_into().unwrap())
                .collect(),
            on_values_vec: generic.on_values[log_heights_f.len() + log_heights_ef.len()..]
                .iter()
                .map(|e| e.to_vec().try_into().unwrap())
                .collect(),
        })
    }
}
