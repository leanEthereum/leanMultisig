/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

*/

use multilinear_toolkit::prelude::*;
use utils::mle_of_01234567_etc;

use tracing::instrument;
use utils::{FSProver, FSVerifier};

use crate::{
    MIN_VARS_FOR_PACKING,
    quotient_gkr::{prove_gkr_quotient, verify_gkr_quotient},
};

#[derive(Debug, PartialEq)]
pub struct LogupStatements<EF> {
    pub on_indexes: Evaluation<EF>,
    pub on_values: Evaluation<EF>,
    pub on_table: Evaluation<EF>,
    pub on_acc: Evaluation<EF>,
}

#[instrument(skip_all)]
pub fn prove_logup<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    indexes: &[PF<EF>],
    values: &[PF<EF>],
    table: &[PF<EF>],
    acc: &[PF<EF>],
    max_index: Option<usize>,
) -> LogupStatements<EF> {
    assert_eq!(table.len(), acc.len());
    assert_eq!(indexes.len(), values.len());

    let packing = log2_strict_usize(table.len()) >= MIN_VARS_FOR_PACKING
        && log2_strict_usize(indexes.len()) >= MIN_VARS_FOR_PACKING;
    let mut max_index = max_index.unwrap_or(table.len());
    if packing {
        max_index = max_index.div_ceil(packing_width::<EF>());
    }
    // TODO use max_index
    let _ = max_index;

    let c = prover_state.sample();
    let alpha = prover_state.sample();

    // Left

    let num_left = vec![EF::ONE; values.len()]; // TODO embedding overhead
    let denom_left = &(0..values.len())
        .into_par_iter()
        .map(|i| c - (alpha * indexes[i] + values[i]))
        .collect::<Vec<_>>();

    let num_left_packed = MleRef::Extension(&num_left).pack_if(packing);
    let denom_left_packed = MleRef::Extension(denom_left).pack_if(packing);

    let (sum_left, claim_point_left, num_left_value, denom_left_value) = prove_gkr_quotient::<_, 2>(
        prover_state,
        &MleGroupRef::merge(&[&num_left_packed.by_ref(), &denom_left_packed.by_ref()]),
    );
    assert_eq!(num_left_value, EF::ONE);
    let eval_on_indexes = indexes.evaluate(&claim_point_left);
    prover_state.add_extension_scalar(eval_on_indexes);
    let eval_on_values = c - denom_left_value - alpha * eval_on_indexes;

    // Right

    let num_right = acc.par_iter().map(|a| EF::from(*a)).collect::<Vec<_>>(); // TODO embedding overhead
    let denom_right = &(0..table.len())
        .into_par_iter()
        .map(|i| c - (alpha * PF::<EF>::from_usize(i) + table[i]))
        .collect::<Vec<_>>();

    let num_right_packed = MleRef::Extension(&num_right).pack_if(packing);
    let denom_right_packed = MleRef::Extension(denom_right).pack_if(packing);

    let (sum_right, claim_point_right, num_right_value, denom_right_value) = prove_gkr_quotient::<_, 2>(
        prover_state,
        &MleGroupRef::merge(&[&num_right_packed.by_ref(), &denom_right_packed.by_ref()]),
    );
    let eval_on_table = c - denom_right_value - alpha * mle_of_01234567_etc(&claim_point_right);

    assert_eq!(sum_left, sum_right);

    // These statements remained to be proven
    LogupStatements {
        on_indexes: Evaluation::new(claim_point_left.clone(), eval_on_indexes),
        on_values: Evaluation::new(claim_point_left, eval_on_values),
        on_acc: Evaluation::new(claim_point_right.clone(), num_right_value),
        on_table: Evaluation::new(claim_point_right, eval_on_table),
    }
}

pub fn verify_logup<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    log_table_len: usize,
    log_indexes_len: usize,
) -> Result<LogupStatements<EF>, ProofError> {
    let c = verifier_state.sample();
    let alpha = verifier_state.sample();

    let (sum_left, claim_point_left, num_left_value, denom_left_value) =
        verify_gkr_quotient::<_, 2>(verifier_state, log_indexes_len)?;
    assert_eq!(num_left_value, EF::ONE);
    let eval_on_indexes = verifier_state.next_extension_scalar()?;
    let eval_on_values = c - denom_left_value - alpha * eval_on_indexes;

    let (sum_right, claim_point_right, num_right_value, denom_right_value) =
        verify_gkr_quotient::<_, 2>(verifier_state, log_table_len)?;
    let eval_on_table = c - denom_right_value - alpha * mle_of_01234567_etc(&claim_point_right);

    if sum_left != sum_right {
        return Err(ProofError::InvalidProof);
    }

    // These statements remained to be verified
    Ok(LogupStatements {
        on_indexes: Evaluation::new(claim_point_left.clone(), eval_on_indexes),
        on_values: Evaluation::new(claim_point_left, eval_on_values),
        on_acc: Evaluation::new(claim_point_right.clone(), num_right_value),
        on_table: Evaluation::new(claim_point_right, eval_on_table),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use utils::{build_prover_state, build_verifier_state, init_tracing};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    #[test]
    fn test_logup() {
        for log_table_len in [3, 10] {
            for log_indexes_len in 3..10 {
                test_logup_helper(log_table_len, log_indexes_len);
            }
        }

        test_logup_helper(12, 14);
    }

    fn test_logup_helper(log_table_len: usize, log_indexes_len: usize) {
        init_tracing();

        let table_length = 1 << log_table_len;

        let indexes_len = 1 << log_indexes_len;

        let mut rng = StdRng::seed_from_u64(0);

        let table = (0..table_length).map(|_| rng.random()).collect::<Vec<F>>();
        let mut acc = vec![F::ZERO; table_length];

        let mut indexes = vec![];
        let mut values = vec![];
        let max_index = table_length * 3 / 4;
        for _ in 0..indexes_len {
            let index = rng.random_range(0..max_index);
            indexes.push(F::from_usize(index));
            values.push(table[index]);
            acc[index] += F::ONE;
        }

        // Commit to the table
        let commited_table = table.clone(); // Phony commitment for the example
        // commit to the indexes
        let commited_indexes = indexes.clone(); // Phony commitment for the example
        // Commit to the values
        let commited_values = values.clone(); // Phony commitment for the example
        // Commit to the accumulator
        let commited_acc = acc.clone(); // Phony commitment for the example

        let mut prover_state = build_prover_state(false);

        let time = std::time::Instant::now();

        let prover_statements = prove_logup::<EF>(
            &mut prover_state,
            &commited_indexes,
            &commited_values,
            &commited_table,
            &commited_acc,
            Some(max_index),
        );
        println!("Proving logup took {} ms", time.elapsed().as_millis());

        let last_prover_state = prover_state.challenger().state();
        let mut verifier_state = build_verifier_state(prover_state);
        let verifier_statements = verify_logup(&mut verifier_state, log_table_len, log_indexes_len).unwrap();

        assert_eq!(&verifier_statements, &prover_statements);
        assert_eq!(last_prover_state, verifier_state.challenger().state());

        assert_eq!(
            indexes.evaluate(&verifier_statements.on_indexes.point),
            verifier_statements.on_indexes.value
        );
        assert_eq!(
            table.evaluate(&verifier_statements.on_table.point),
            verifier_statements.on_table.value
        );
        assert_eq!(
            acc.evaluate(&verifier_statements.on_acc.point),
            verifier_statements.on_acc.value
        );
        assert_eq!(
            values.evaluate(&verifier_statements.on_values.point),
            verifier_statements.on_values.value
        );
    }
}
