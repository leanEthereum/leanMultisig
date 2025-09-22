/*
Logup* (Lev Soukhanov)

https://eprint.iacr.org/2025/946.pdf

*/

use p3_field::{ExtensionField, Field, PrimeField64};
use rayon::prelude::*;
use utils::ToUsize;

use p3_field::PrimeCharacteristicRing;
use sumcheck::{MleGroupRef, ProductComputation};
use tracing::{info_span, instrument};
use utils::{EFPacking, FSProver, FSVerifier, PF, pack_extension, packing_width};
use whir_p3::fiat_shamir::FSChallenger;
use whir_p3::poly::multilinear::{Evaluation, MultilinearPoint};
use whir_p3::utils::parallel_clone;
use whir_p3::{fiat_shamir::errors::ProofError, utils::uninitialized_vec};

use crate::quotient_gkr::{prove_gkr_quotient, verify_gkr_quotient};

#[derive(Debug)]
pub struct LogupStarStatements<EF> {
    pub on_indexes: Evaluation<EF>,
    pub on_table: Evaluation<EF>,
    pub on_pushforward: Vec<Evaluation<EF>>,
}

#[instrument(skip_all)]
pub fn prove_logup_star<IF, EF>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    table: &[IF],
    indexes: &[PF<EF>],
    claimed_value: EF,
    poly_eq_point: &[EF],
    pushforward: &[EF], // already commited
) -> LogupStarStatements<EF>
where
    IF: Field,
    EF: ExtensionField<PF<EF>> + ExtensionField<IF>,
    PF<EF>: PrimeField64,
{
    let table_length = table.len();
    let indexes_length = indexes.len();

    let table_embedded = info_span!("embedding")
        .in_scope(|| table.par_iter().map(|&x| EF::from(x)).collect::<Vec<_>>());

    let (table_embedded_packed, poly_eq_point_packed, pushforward_packed) = info_span!("packing")
        .in_scope(|| {
            (
                pack_extension(&table_embedded),
                pack_extension(poly_eq_point),
                pack_extension(pushforward),
            )
        });

    let (sc_point, inner_evals, prod) =
        info_span!("logup_star sumcheck", table_length, indexes_length).in_scope(|| {
            sumcheck::prove::<EF, _, _, _>(
                1,
                MleGroupRef::ExtensionPacked(vec![&table_embedded_packed, &pushforward_packed]),
                &ProductComputation,
                &ProductComputation,
                &[],
                None,
                false,
                prover_state,
                claimed_value,
                None,
            )
        });

    let table_eval = inner_evals[0];
    prover_state.add_extension_scalar(table_eval);
    // delayed opening
    let on_table = Evaluation::new(sc_point.clone(), table_eval);

    let pushforwardt_eval = inner_evals[1];
    prover_state.add_extension_scalar(pushforwardt_eval);
    // delayed opening
    let mut on_pushforward = vec![Evaluation::new(sc_point, pushforwardt_eval)];

    // sanity check
    assert_eq!(prod, table_eval * pushforwardt_eval);

    // "c" in the paper
    let random_challenge = prover_state.sample();

    let gkr_layer_left = info_span!("building left").in_scope(|| {
        let mut layer = unsafe {
            uninitialized_vec::<EFPacking<EF>>(indexes_length * 2 / packing_width::<EF>())
        };
        let half_len_packed = layer.len() / 2;
        let challenge_minus_indexes = pack_extension(
            &indexes
                .par_iter()
                .map(|&x| random_challenge - x)
                .collect::<Vec<_>>(),
        );
        parallel_clone(&poly_eq_point_packed, &mut layer[..half_len_packed]);
        parallel_clone(&challenge_minus_indexes, &mut layer[half_len_packed..]);
        layer
    });

    let (claim_left, _, eval_c_minux_indexes) = prove_gkr_quotient(prover_state, gkr_layer_left);

    let gkr_layer_right = info_span!("building right").in_scope(|| {
        let mut layer =
            unsafe { uninitialized_vec::<EFPacking<EF>>(table_length * 2 / packing_width::<EF>()) };
        let half_len_packed = layer.len() / 2;
        let challenge_minus_increment = pack_extension(
            &(0..table.len())
                .into_par_iter()
                .map(|i| random_challenge - PF::<EF>::from_usize(i))
                .collect::<Vec<_>>(),
        );
        parallel_clone(&pushforward_packed, &mut layer[..half_len_packed]);
        parallel_clone(&challenge_minus_increment, &mut layer[half_len_packed..]);
        layer
    });
    let (claim_right, pushforward_final_eval, _) =
        prove_gkr_quotient(prover_state, gkr_layer_right);

    let final_point_left = claim_left.point[1..].to_vec();
    let indexes_final_eval = random_challenge - eval_c_minux_indexes;
    prover_state.add_extension_scalar(indexes_final_eval);
    let on_indexes = Evaluation::new(final_point_left, indexes_final_eval);

    prover_state.add_extension_scalar(pushforward_final_eval);
    on_pushforward.push(Evaluation::new(
        claim_right.point[1..].to_vec(),
        pushforward_final_eval,
    ));

    // These statements remained to be proven
    LogupStarStatements {
        on_indexes,
        on_table,
        on_pushforward,
    }
}

pub fn verify_logup_star<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    log_table_len: usize,
    log_indexes_len: usize,
    claims: &[Evaluation<EF>],
    alpha: EF, // batching challenge
) -> Result<LogupStarStatements<EF>, ProofError>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: PrimeField64,
{
    let (sum, postponed) =
        sumcheck::verify(verifier_state, log_table_len, 2).map_err(|_| ProofError::InvalidProof)?;

    if sum
        != claims
            .iter()
            .zip(alpha.powers())
            .map(|(c, a)| c.value * a)
            .sum::<EF>()
    {
        return Err(ProofError::InvalidProof);
    }

    let table_eval = verifier_state.next_extension_scalar()?;
    let pushforward_eval = verifier_state.next_extension_scalar()?;

    let on_table = Evaluation::new(postponed.point.clone(), table_eval);
    let mut on_pushforward = vec![Evaluation::new(postponed.point, pushforward_eval)];

    if table_eval * pushforward_eval != postponed.value {
        return Err(ProofError::InvalidProof);
    }

    let random_challenge = verifier_state.sample(); // "c" in the paper

    let (quotient_left, claim_left) = verify_gkr_quotient(verifier_state, log_indexes_len + 1)?;
    let (quotient_right, claim_right) = verify_gkr_quotient(verifier_state, log_table_len + 1)?;

    if quotient_left != quotient_right {
        return Err(ProofError::InvalidProof);
    }

    let final_point_left = MultilinearPoint(claim_left.point[1..].to_vec());
    let index_openined_value = verifier_state.next_extension_scalar()?;
    let on_indexes = Evaluation::new(final_point_left.clone(), index_openined_value);
    if claim_left.value
        != claims
            .iter()
            .zip(alpha.powers())
            .map(|(claim, a)| final_point_left.eq_poly_outside(&claim.point) * a)
            .sum::<EF>()
            * (EF::ONE - claim_left.point[0])
            + (random_challenge - index_openined_value) * claim_left.point[0]
    {
        return Err(ProofError::InvalidProof);
    }

    let final_point_right = claim_right.point[1..].to_vec();
    let pushforward_opening_value = verifier_state.next_extension_scalar()?;
    on_pushforward.push(Evaluation::new(
        final_point_right.clone(),
        pushforward_opening_value,
    ));

    let big_endian_mle = final_point_right
        .iter()
        .rev()
        .enumerate()
        .map(|(i, &p)| p * EF::TWO.exp_u64(i as u64))
        .sum::<EF>();

    if claim_right.value
        != pushforward_opening_value * (EF::ONE - claim_right.point[0])
            + (random_challenge - big_endian_mle) * claim_right.point[0]
    {
        return Err(ProofError::InvalidProof);
    }

    // these statements remained to be verified
    Ok(LogupStarStatements {
        on_indexes,
        on_table,
        on_pushforward,
    })
}

#[instrument(skip_all)]
pub fn compute_pushforward<F: PrimeField64, EF: ExtensionField<EF>>(
    indexes: &[F],
    table_length: usize,
    poly_eq_point: &[EF],
) -> Vec<EF> {
    assert_eq!(indexes.len(), poly_eq_point.len());
    // TODO there are a lot of fun optimizations here
    let mut pushforward = EF::zero_vec(table_length);
    for (index, value) in indexes.iter().zip(poly_eq_point) {
        let index_usize = index.to_usize();
        pushforward[index_usize] += *value;
    }
    pushforward
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;
    use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use utils::{build_challenger, init_tracing};
    use whir_p3::poly::evals::{EvaluationsList, eval_eq};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    #[test]
    fn test_logup_star() {
        init_tracing();

        let log_table_len = 19;
        let table_length = 1 << log_table_len;

        let log_indexes_len = log_table_len + 2;
        let indexes_len = 1 << log_indexes_len;

        let mut rng = StdRng::seed_from_u64(0);

        let table = (0..table_length).map(|_| rng.random()).collect::<Vec<F>>();

        let mut indexes = vec![];
        let mut values = vec![];
        for _ in 0..indexes_len {
            let index = rng.random_range(0..table_length);
            indexes.push(F::from_usize(index));
            values.push(table[index]);
        }

        // Commit to the table
        let commited_table = table.clone(); // Phony commitment for the example
        // commit to the indexes
        let commited_indexes = indexes.clone(); // Phony commitment for the example

        let challenger = build_challenger();

        let point = MultilinearPoint(
            (0..log_indexes_len)
                .map(|_| rng.random())
                .collect::<Vec<EF>>(),
        );

        let mut prover_state = FSProver::new(challenger.clone());
        let eval = values.evaluate(&point);

        let time = std::time::Instant::now();
        let poly_eq_point = info_span!("eval_eq").in_scope(|| eval_eq(&point));
        let pushforward = compute_pushforward(&indexes, table_length, &poly_eq_point);
        let claim = Evaluation::new(point, eval);

        prove_logup_star(
            &mut prover_state,
            &commited_table,
            &commited_indexes,
            claim.value,
            &poly_eq_point,
            &pushforward,
        );
        println!("Proving logup_star took {} ms", time.elapsed().as_millis());

        let mut verifier_state = FSVerifier::new(prover_state.proof_data().to_vec(), challenger);
        let statements = verify_logup_star(
            &mut verifier_state,
            log_table_len,
            log_indexes_len,
            &[claim],
            EF::ONE,
        )
        .unwrap();

        assert_eq!(
            indexes.evaluate(&statements.on_indexes.point),
            statements.on_indexes.value
        );
        assert_eq!(
            table.evaluate(&statements.on_table.point),
            statements.on_table.value
        );
        for eval in &statements.on_pushforward {
            assert_eq!(pushforward.evaluate(&eval.point), eval.value);
        }
    }
}
