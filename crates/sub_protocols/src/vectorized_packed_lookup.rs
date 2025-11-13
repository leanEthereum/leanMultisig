use multilinear_toolkit::prelude::*;
use utils::FSProver;
use utils::VecOrSlice;
use utils::fold_multilinear_chunks;

use crate::GenericPackedLookupProver;
use crate::GenericPackedLookupVerifier;
use crate::PackedLookupStatements;

#[derive(Debug)]
pub struct VectorizedPackedLookupProver<'a, EF: ExtensionField<PF<EF>>, const VECTOR_LEN: usize> {
    generic: GenericPackedLookupProver<'a, EF, EF>,
    folding_scalars: MultilinearPoint<EF>,
}

impl<'a, EF: ExtensionField<PF<EF>>, const VECTOR_LEN: usize>
    VectorizedPackedLookupProver<'a, EF, VECTOR_LEN>
where
    PF<EF>: PrimeField64,
{
    pub fn pushforward_to_commit(&self) -> &[EF] {
        self.generic.pushforward_to_commit()
    }

    // before committing to the pushforward
    pub fn step_1(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        table: &'a [PF<EF>], // table[0] is assumed to be zero
        index_columns: Vec<&'a [PF<EF>]>,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        value_columns: Vec<&'a [Vec<PF<EF>>; VECTOR_LEN]>,
        statements: Vec<Vec<MultiEvaluation<EF>>>,
        log_smallest_decomposition_chunk: usize,
    ) -> Self {
        let folding_scalars =
            MultilinearPoint(prover_state.sample_vec(log2_strict_usize(VECTOR_LEN)));
        let folded_table = fold_multilinear_chunks(&table, &folding_scalars);

        let folding_poly_eq = eval_eq(&folding_scalars);
        let folded_value_columns = value_columns
            .par_iter()
            .map(|cols| {
                let n = cols[0].len();
                assert!(cols.iter().all(|c| c.len() == n));
                assert!(n.is_power_of_two());
                vec![VecOrSlice::Vec(
                    (0..n)
                        .into_par_iter()
                        .map(|i| {
                            folding_poly_eq
                                .iter()
                                .enumerate()
                                .map(|(j, &coeff)| coeff * cols[j][i])
                                .sum::<EF>()
                        })
                        .collect::<Vec<_>>(),
                )]
            })
            .collect::<Vec<_>>();

        let generic = GenericPackedLookupProver::<'_, EF, EF>::step_1(
            prover_state,
            VecOrSlice::Vec(folded_table),
            index_columns,
            heights,
            default_indexes,
            folded_value_columns,
            get_folded_statements(statements, &folding_scalars),
            log_smallest_decomposition_chunk,
        );

        Self {
            generic,
            folding_scalars,
        }
    }

    // after committing to the pushforward
    pub fn step_2(
        &self,
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
        non_zero_memory_size: usize,
    ) -> PackedLookupStatements<EF> {
        let mut statements = self
            .generic
            .step_2(prover_state, non_zero_memory_size.div_ceil(VECTOR_LEN));
        statements
            .on_table
            .point
            .extend(self.folding_scalars.0.clone());
        statements
    }
}

#[derive(Debug)]
pub struct VectorizedPackedLookupVerifier<EF: ExtensionField<PF<EF>>, const VECTOR_LEN: usize> {
    generic: GenericPackedLookupVerifier<EF>,
    folding_scalars: MultilinearPoint<EF>,
}

impl<EF: ExtensionField<PF<EF>>, const VECTOR_LEN: usize>
    VectorizedPackedLookupVerifier<EF, VECTOR_LEN>
where
    PF<EF>: PrimeField64,
{
    // before receiving the commitment to the pushforward
    pub fn step_1(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        heights: Vec<usize>,
        default_indexes: Vec<usize>,
        statements: Vec<Vec<MultiEvaluation<EF>>>,
        log_smallest_decomposition_chunk: usize,
        table_initial_values: &[PF<EF>],
    ) -> ProofResult<Self> {
        let folding_scalars =
            MultilinearPoint(verifier_state.sample_vec(log2_strict_usize(VECTOR_LEN)));
        let folded_table_initial_values = fold_multilinear_chunks(
            &table_initial_values[..(table_initial_values.len() / VECTOR_LEN) * VECTOR_LEN],
            &folding_scalars,
        );

        let generic = GenericPackedLookupVerifier::step_1::<EF>(
            verifier_state,
            heights,
            default_indexes,
            get_folded_statements(statements, &folding_scalars),
            log_smallest_decomposition_chunk,
            &folded_table_initial_values,
        )?;

        Ok(Self {
            generic,
            folding_scalars,
        })
    }

    // after receiving the commitment to the pushforward
    pub fn step_2(
        &self,
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        log_memory_size: usize,
    ) -> ProofResult<PackedLookupStatements<EF>> {
        let mut statements = self.generic.step_2(
            verifier_state,
            log_memory_size - log2_strict_usize(VECTOR_LEN),
        )?;
        statements
            .on_table
            .point
            .extend(self.folding_scalars.0.clone());
        Ok(statements)
    }
}

fn get_folded_statements<EF: Field>(
    statements: Vec<Vec<MultiEvaluation<EF>>>,
    folding_scalars: &MultilinearPoint<EF>,
) -> Vec<Vec<MultiEvaluation<EF>>> {
    statements
        .iter()
        .map(|sub_statements| {
            sub_statements
                .iter()
                .map(|meval| {
                    MultiEvaluation::new(
                        meval.point.clone(),
                        vec![meval.values.evaluate(&folding_scalars)],
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
}
