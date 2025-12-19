use multilinear_toolkit::prelude::*;
use utils::VecOrSlice;
use utils::transpose_slice_to_basis_coefficients;

use crate::{GeneralizedLogupProver, GeneralizedLogupVerifier};

#[derive(Debug)]
pub struct CustomLookupProver;

/// claims contain sparse points (TODO take advantage of it)
#[derive(Debug, PartialEq)]
pub struct CustomLookupStatements<EF, const DIM: usize> {
    pub on_table: Evaluation<EF>,
    pub on_acc: Evaluation<EF>,
    pub on_indexes_f: Vec<Evaluation<EF>>,
    pub on_indexes_ef: Vec<Evaluation<EF>>,
    pub on_values_f: Vec<Vec<Evaluation<EF>>>,
    pub on_values_ef: Vec<[Evaluation<EF>; DIM]>,

    // buses
    pub on_bus_numerators: Vec<Evaluation<EF>>,
    pub on_bus_denominators: Vec<Evaluation<EF>>,
}

impl CustomLookupProver {
    #[allow(clippy::too_many_arguments)]
    pub fn run<EF: ExtensionField<PF<EF>>, const DIM: usize>(
        prover_state: &mut impl FSProver<EF>,
        c: EF,
        alpha: EF,
        table: &[PF<EF>], // table[0] is assumed to be zero
        acc: &[PF<EF>],
        index_columns_f: Vec<&[PF<EF>]>,
        index_columns_ef: Vec<&[PF<EF>]>,
        value_columns_f: Vec<Vec<&[PF<EF>]>>,
        value_columns_ef: Vec<&[EF]>,

        // parameters for "buses" = information flow between different tables
        bus_numerators: Vec<&[PF<EF>]>,
        bus_denominators: Vec<&[EF]>,
        univariate_skips: usize,
    ) -> CustomLookupStatements<EF, DIM> {
        assert_eq!(index_columns_f.len(), value_columns_f.len(),);
        assert_eq!(index_columns_ef.len(), value_columns_ef.len(),);
        let n_cols_f = value_columns_f.len();

        let mut all_value_columns = vec![];
        for cols_f in value_columns_f {
            all_value_columns.push(cols_f.iter().map(|s| VecOrSlice::Slice(s)).collect());
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

        let generic = GeneralizedLogupProver::run(
            prover_state,
            c,
            alpha,
            table,
            acc,
            index_columns,
            all_value_columns,
            bus_numerators,
            bus_denominators,
            univariate_skips,
        );

        CustomLookupStatements {
            on_table: generic.on_table,
            on_acc: generic.on_acc,
            on_indexes_f: generic.on_indexes[..n_cols_f].to_vec(),
            on_indexes_ef: generic.on_indexes[n_cols_f..].to_vec(),
            on_values_f: generic.on_values[..n_cols_f].to_vec(),
            on_values_ef: generic.on_values[n_cols_f..]
                .iter()
                .map(|e| e.to_vec().try_into().unwrap())
                .collect(),
            on_bus_numerators: generic.on_bus_numerators,
            on_bus_denominators: generic.on_bus_denominators,
        }
    }
}

#[derive(Debug)]
pub struct NormalLookupVerifier;

impl NormalLookupVerifier {
    #[allow(clippy::too_many_arguments)]
    pub fn run<EF: ExtensionField<PF<EF>>, const DIM: usize>(
        verifier_state: &mut impl FSVerifier<EF>,
        c: EF,
        alpha: EF,
        log_memory: usize,
        log_heights_f: Vec<usize>,
        num_values_per_lookup_f: Vec<usize>,
        log_heights_ef: Vec<usize>,
        bus_n_vars: Vec<usize>,
        univariate_skips: usize,
    ) -> ProofResult<CustomLookupStatements<EF, DIM>> {
        assert_eq!(log_heights_f.len(), num_values_per_lookup_f.len());
        let log_heights = [log_heights_f.clone(), log_heights_ef.clone()].concat();
        let n_cols_per_group = [num_values_per_lookup_f, vec![DIM; log_heights_ef.len()]].concat();
        let generic = GeneralizedLogupVerifier::run(
            verifier_state,
            c,
            alpha,
            log_memory,
            log_heights,
            n_cols_per_group,
            bus_n_vars,
            univariate_skips,
        )?;

        Ok(CustomLookupStatements {
            on_table: generic.on_table,
            on_acc: generic.on_acc,
            on_indexes_f: generic.on_indexes[..log_heights_f.len()].to_vec(),
            on_indexes_ef: generic.on_indexes[log_heights_f.len()..].to_vec(),
            on_values_f: generic.on_values[..log_heights_f.len()].to_vec(),
            on_values_ef: generic.on_values[log_heights_f.len()..][..log_heights_ef.len()]
                .iter()
                .map(|e| e.to_vec().try_into().unwrap())
                .collect(),
            on_bus_numerators: generic.on_bus_numerators,
            on_bus_denominators: generic.on_bus_denominators,
        })
    }
}
