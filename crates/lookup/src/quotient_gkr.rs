use std::array;

use multilinear_toolkit::prelude::*;
use tracing::instrument;
use utils::{FSProver, FSVerifier};

use crate::MIN_VARS_FOR_PACKING;

/*
GKR to compute sum of fractions.
*/

#[instrument(skip_all)]
pub fn prove_gkr_quotient<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    numerators_and_denominators: &MleGroupRef<'_, EF>,
) -> (MultilinearPoint<EF>, EF, EF) {
    assert_eq!(numerators_and_denominators.n_columns(), 2);
    let mut layers = vec![MleGroup::Ref(numerators_and_denominators.soft_clone())];

    for i in 0.. {
        let prev_layer: MleGroup<'_, EF> = layers.last().unwrap().by_ref().into();
        let prev_layer = if prev_layer.is_packed() && prev_layer.n_vars() < MIN_VARS_FOR_PACKING {
            prev_layer.by_ref().unpack().as_owned_or_clone().into()
        } else {
            prev_layer
        };
        if prev_layer.n_vars() == 1 {
            break;
        }
        if i == 0 {
            layers.push(sum_quotients::<EF, N_GROUPS>(prev_layer.by_ref()).into());
        } else {
            layers.push(sum_quotients::<EF, 2>(prev_layer.by_ref()).into());
        }
    }

    let last_layer = layers.pop().unwrap();
    let last_layer = last_layer.as_owned_or_clone().as_extension().unwrap();

    assert_eq!(last_layer.len(), 2);
    let last_nums: [_; 2] = last_layer[0].clone().try_into().unwrap();
    let last_dens: [_; 2] = last_layer[1].clone().try_into().unwrap();
    prover_state.add_extension_scalars(&last_nums);
    prover_state.add_extension_scalars(&last_dens);

    let mut point = MultilinearPoint(vec![prover_state.sample()]);
    let mut claim_num = last_nums.evaluate(&point);
    let mut claim_den = last_dens.evaluate(&point);

    for layer in layers[1..].iter().rev() {
        (point, claim_num, claim_den) = prove_gkr_quotient_step::<_, 2>(
            prover_state,
            layer.by_ref(),
            &point,
            claim_num,
            claim_den,
        );
    }
    (point, claim_num, claim_den) = prove_gkr_quotient_step::<_, N_GROUPS>(
        prover_state,
        layers[0].by_ref(),
        &point,
        claim_num,
        claim_den,
    );

    (point, claim_num, claim_den)
}

fn prove_gkr_quotient_step<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    numerators_and_denominators: MleGroupRef<'_, EF>,
    claim_point: &MultilinearPoint<EF>,
    claim_num: EF,
    claim_den: EF,
) -> (MultilinearPoint<EF>, EF, EF) {
    let numerators_and_denominators_split = match numerators_and_denominators {
        MleGroupRef::Extension(numerators_and_denominators) => {
            MleGroupRef::Extension(split_chunks::<_, N_GROUPS>(&numerators_and_denominators))
        }
        MleGroupRef::ExtensionPacked(numerators_and_denominators) => {
            MleGroupRef::ExtensionPacked(split_chunks::<_, N_GROUPS>(&numerators_and_denominators))
        }
        _ => unreachable!(),
    };

    let alpha = prover_state.sample();

    let (mut next_claim_point, inner_evals, _) = sumcheck_prove::<EF, _, _>(
        1,
        numerators_and_denominators_split,
        &GKRQuotientComputation::<N_GROUPS> {},
        &[alpha],
        Some((claim_point.0.clone(), None)),
        false,
        prover_state,
        claim_num + alpha * claim_den,
        false,
    );
    prover_state.add_extension_scalars(&inner_evals);
    let beta = prover_state.sample();
    let selectors = univariate_selectors(log2_strict_usize(N_GROUPS));
    let next_claim_numerator = evaluate_univariate_multilinear::<_, _, _, false>(
        &inner_evals[..N_GROUPS],
        &[beta],
        &selectors,
        None,
    );
    let next_claim_denominator = evaluate_univariate_multilinear::<_, _, _, false>(
        &inner_evals[N_GROUPS..],
        &[beta],
        &selectors,
        None,
    );
    next_claim_point.0.insert(0, beta);

    (
        next_claim_point,
        next_claim_numerator,
        next_claim_denominator,
    )
}

pub fn verify_gkr_quotient<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_vars: usize,
) -> Result<(EF, MultilinearPoint<EF>, EF, EF), ProofError> {
    let [num_left, num_right] = verifier_state.next_extension_scalars_const()?;
    let [den_left, den_right] = verifier_state.next_extension_scalars_const()?;
    if den_left == EF::ZERO || den_right == EF::ZERO {
        return Err(ProofError::InvalidProof);
    }
    let quotient = num_left / den_left + num_right / den_right;

    let mut point = MultilinearPoint(vec![verifier_state.sample()]);
    let mut claim_num = [num_left, num_right].evaluate(&point);
    let mut claim_den = [den_left, den_right].evaluate(&point);

    for i in 1..n_vars - log2_strict_usize(N_GROUPS) {
        (point, claim_num, claim_den) =
            verify_gkr_quotient_step::<_, 2>(verifier_state, i, &point, claim_num, claim_den)?;
    }
    (point, claim_num, claim_den) = verify_gkr_quotient_step::<_, N_GROUPS>(
        verifier_state,
        n_vars - log2_strict_usize(N_GROUPS),
        &point,
        claim_num,
        claim_den,
    )?;

    Ok((quotient, point, claim_num, claim_den))
}

fn verify_gkr_quotient_step<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_vars: usize,
    point: &MultilinearPoint<EF>,
    claim_num: EF,
    claim_den: EF,
) -> Result<(MultilinearPoint<EF>, EF, EF), ProofError> {
    let alpha = verifier_state.sample();

    let (retrieved_quotient, postponed) = sumcheck_verify(verifier_state, n_vars, 1 + N_GROUPS)?;

    if retrieved_quotient != claim_num + alpha * claim_den {
        return Err(ProofError::InvalidProof);
    }

    let inner_evals = verifier_state.next_extension_scalars_vec(N_GROUPS * 2)?;

    if postponed.value
        != point.eq_poly_outside(&postponed.point)
            * <GKRQuotientComputation<N_GROUPS> as SumcheckComputation<EF>>::eval_extension(
                &Default::default(),
                &inner_evals,
                &[alpha],
            )
    {
        return Err(ProofError::InvalidProof);
    }

    let beta = verifier_state.sample();
    let selectors = univariate_selectors(log2_strict_usize(N_GROUPS));
    let next_claim_numerator = evaluate_univariate_multilinear::<_, _, _, false>(
        &inner_evals[..N_GROUPS],
        &[beta],
        &selectors,
        None,
    );
    let next_claim_denominator = evaluate_univariate_multilinear::<_, _, _, false>(
        &inner_evals[N_GROUPS..],
        &[beta],
        &selectors,
        None,
    );
    let mut next_claim_point = postponed.point.clone();
    next_claim_point.0.insert(0, beta);

    Ok((
        next_claim_point,
        next_claim_numerator,
        next_claim_denominator,
    ))
}

fn sum_quotients<EF: ExtensionField<PF<EF>>, const N_GROUPS: usize>(
    numerators_and_denominators: MleGroupRef<'_, EF>,
) -> MleGroupOwned<EF> {
    match numerators_and_denominators {
        MleGroupRef::ExtensionPacked(numerators_and_denominators) => {
            assert_eq!(numerators_and_denominators.len(), 2);
            MleGroupOwned::ExtensionPacked(sum_quotients_helper::<_, N_GROUPS>(
                &numerators_and_denominators[0],
                &numerators_and_denominators[1],
            ))
            .into()
        }
        MleGroupRef::Extension(numerators_and_denominators) => {
            assert_eq!(numerators_and_denominators.len(), 2);
            MleGroupOwned::Extension(sum_quotients_helper::<_, N_GROUPS>(
                &numerators_and_denominators[0],
                &numerators_and_denominators[1],
            ))
            .into()
        }
        _ => unreachable!(),
    }
}
fn sum_quotients_helper<F: PrimeCharacteristicRing + Sync + Send + Copy, const N: usize>(
    numerators: &[F],
    denominators: &[F],
) -> Vec<Vec<F>> {
    let n = numerators.len();
    let new_n = n / N;
    let mut new_numerators = unsafe { uninitialized_vec(new_n) };
    let mut new_denominators = unsafe { uninitialized_vec(new_n) };
    new_numerators
        .par_iter_mut()
        .zip(new_denominators.par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            let my_numerators: [_; N] = array::from_fn(|j| numerators[i + new_n * j]);
            let my_denominators: [_; N] = array::from_fn(|j| denominators[i + new_n * j]);
            *num = numerator_of_sum_of_quotients::<N, _>(&my_numerators, &my_denominators);
            *den = mul_many_const::<N, _>(&my_denominators);
        });
    vec![new_numerators, new_denominators]
}
fn split_chunks<'a, A, const N_GROUPS: usize>(
    numerators_and_denominators: &[&'a [A]],
) -> Vec<&'a [A]> {
    assert_eq!(numerators_and_denominators.len(), 2);
    let numerators = &numerators_and_denominators[0];
    let denominators = &numerators_and_denominators[1];
    let n = numerators.len();
    assert_eq!(n, denominators.len());
    assert!(n.is_power_of_two() && n >= N_GROUPS);

    let numerator_chunks = split_at_many(
        &numerators,
        &(1..N_GROUPS).map(|i| i * n / N_GROUPS).collect::<Vec<_>>(),
    );
    let denominator_chunks = split_at_many(
        &denominators,
        &(1..N_GROUPS).map(|i| i * n / N_GROUPS).collect::<Vec<_>>(),
    );

    [numerator_chunks, denominator_chunks].concat()
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;
    use p3_koala_bear::QuinticExtensionFieldKB;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use utils::{build_prover_state, build_verifier_state, init_tracing};

    type EF = QuinticExtensionFieldKB;

    fn sum_all_quotients(nums: &[EF], den: &[EF]) -> EF {
        nums.iter().zip(den.iter()).map(|(&n, &d)| n / d).sum()
    }

    const N_GROUPS: usize = 2;

    #[test]
    fn test_gkr_quotient() {
        let log_n = 22;
        let n = 1 << log_n;
        init_tracing();

        let mut rng = StdRng::seed_from_u64(0);

        let numerators = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let c: EF = rng.random();
        let denominators_indexes = (0..n)
            .map(|_| PF::<EF>::from_usize(rng.random_range(..n)))
            .collect::<Vec<_>>();
        let denominators = denominators_indexes
            .iter()
            .map(|&i| c - i)
            .collect::<Vec<EF>>();
        let real_quotient = sum_all_quotients(&numerators, &denominators);
        let mut prover_state = build_prover_state();

        let time = Instant::now();
        let prover_statements = prove_gkr_quotient::<EF, N_GROUPS>(
            &mut prover_state,
            &MleGroupRef::ExtensionPacked(vec![
                &pack_extension(&numerators),
                &pack_extension(&denominators),
            ]),
        );
        println!("Proving time: {:?}", time.elapsed());

        let mut verifier_state = build_verifier_state(&prover_state);

        let (retrieved_quotient, claim_point, claim_num, claim_den) =
            verify_gkr_quotient::<EF, N_GROUPS>(&mut verifier_state, log_n).unwrap();

        assert_eq!(&prover_statements.0, &claim_point);
        assert_eq!(prover_statements.1, claim_num);
        assert_eq!(prover_statements.2, claim_den);

        assert_eq!(retrieved_quotient, real_quotient);
        let selectors = univariate_selectors::<PF<EF>>(log2_strict_usize(N_GROUPS));
        assert_eq!(
            evaluate_univariate_multilinear::<_, _, _, true>(
                &numerators,
                &claim_point,
                &selectors,
                None
            ),
            claim_num
        );
        assert_eq!(
            evaluate_univariate_multilinear::<_, _, _, true>(
                &denominators,
                &claim_point,
                &selectors,
                None
            ),
            claim_den
        );
    }
}
