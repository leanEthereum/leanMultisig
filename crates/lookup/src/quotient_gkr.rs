use multilinear_toolkit::prelude::*;
use tracing::instrument;
use utils::{FSProver, FSVerifier};

use crate::MIN_VARS_FOR_PACKING;

/*
GKR to compute sum of fractions.
*/

#[instrument(skip_all)]
pub fn prove_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    numerators_and_denominators: &MleGroupRef<'_, EF>,
) -> (MultilinearPoint<EF>, EF, EF) {
    assert_eq!(numerators_and_denominators.n_columns(), 2);
    let mut layers = vec![MleGroup::Ref(numerators_and_denominators.soft_clone())];
    loop {
        let prev_layer: MleGroup<'_, EF> = layers.last().unwrap().by_ref().into();
        let prev_layer = if prev_layer.is_packed() && prev_layer.n_vars() < MIN_VARS_FOR_PACKING {
            prev_layer.by_ref().unpack().as_owned_or_clone().into()
        } else {
            prev_layer
        };
        if prev_layer.n_vars() == 1 {
            break;
        }
        layers.push(match prev_layer.by_ref() {
            MleGroupRef::ExtensionPacked(prev_layer) => {
                assert_eq!(prev_layer.len(), 2);
                MleGroupOwned::ExtensionPacked(sum_quotients_2_by_2(&prev_layer[0], &prev_layer[1]))
                    .into()
            }
            MleGroupRef::Extension(prev_layer) => {
                assert_eq!(prev_layer.len(), 2);
                MleGroupOwned::Extension(sum_quotients_2_by_2(&prev_layer[0], &prev_layer[1]))
                    .into()
            }
            _ => unreachable!(),
        })
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

    for layer in layers.iter().rev() {
        (point, claim_num, claim_den) =
            prove_gkr_quotient_step(prover_state, layer.by_ref(), &point, claim_num, claim_den);
    }

    (point, claim_num, claim_den)
}

fn prove_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    numerators_and_denominators: MleGroupRef<'_, EF>,
    claim_point: &MultilinearPoint<EF>,
    claim_num: EF,
    claim_den: EF,
) -> (MultilinearPoint<EF>, EF, EF) {
    let numerators_and_denominators_split = match numerators_and_denominators {
        MleGroupRef::Extension(numerators_and_denominators) => {
            assert_eq!(numerators_and_denominators.len(), 2);
            let numerators = &numerators_and_denominators[0];
            let denominators = &numerators_and_denominators[1];
            let n = numerators.len();
            assert_eq!(n, denominators.len());
            assert!(n.is_power_of_two() && n >= 2);

            let numerators_left = &numerators[..n / 2];
            let numerators_right = &numerators[n / 2..];
            let denominators_left = &denominators[..n / 2];
            let denominators_right = &denominators[n / 2..];

            MleGroupRef::Extension(vec![
                numerators_left,
                numerators_right,
                denominators_left,
                denominators_right,
            ])
        }
        MleGroupRef::ExtensionPacked(numerators_and_denominators) => {
            assert_eq!(numerators_and_denominators.len(), 2);
            let numerators = &numerators_and_denominators[0];
            let denominators = &numerators_and_denominators[1];
            let n = numerators.len();
            assert_eq!(n, denominators.len());
            assert!(n.is_power_of_two() && n >= 2);

            let numerators_left = &numerators[..n / 2];
            let numerators_right = &numerators[n / 2..];
            let denominators_left = &denominators[..n / 2];
            let denominators_right = &denominators[n / 2..];

            MleGroupRef::ExtensionPacked(vec![
                numerators_left,
                numerators_right,
                denominators_left,
                denominators_right,
            ])
        }
        _ => unreachable!(),
    };

    let alpha = prover_state.sample();

    let (mut next_claim_point, inner_evals, _) = sumcheck_prove::<EF, _, _>(
        1,
        numerators_and_denominators_split,
        &GKRQuotientComputation {},
        &[alpha],
        Some((claim_point.0.clone(), None)),
        false,
        prover_state,
        claim_num + alpha * claim_den,
        true,
    );
    prover_state.add_extension_scalars(&inner_evals);
    let beta = prover_state.sample();
    let next_claim_numerator = inner_evals[0] * (EF::ONE - beta) + inner_evals[1] * beta;
    let next_claim_denominator = inner_evals[2] * (EF::ONE - beta) + inner_evals[3] * beta;
    next_claim_point.0.insert(0, beta);

    (
        next_claim_point,
        next_claim_numerator,
        next_claim_denominator,
    )
}

pub fn verify_gkr_quotient<EF: ExtensionField<PF<EF>>>(
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

    for i in 1..n_vars {
        (point, claim_num, claim_den) =
            verify_gkr_quotient_step(verifier_state, i, &point, claim_num, claim_den)?;
    }

    Ok((quotient, point, claim_num, claim_den))
}

fn verify_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_vars: usize,
    point: &MultilinearPoint<EF>,
    claim_num: EF,
    claim_den: EF,
) -> Result<(MultilinearPoint<EF>, EF, EF), ProofError> {
    let alpha = verifier_state.sample();
    let (retrieved_quotient, postponed) =
        sumcheck_verify(verifier_state, n_vars, 3).map_err(|_| ProofError::InvalidProof)?;

    if retrieved_quotient != claim_num + alpha * claim_den {
        return Err(ProofError::InvalidProof);
    }

    let [next_num_left, next_num_right, next_den_left, next_den_right] =
        verifier_state.next_extension_scalars_const()?;

    if postponed.value
        != point.eq_poly_outside(&postponed.point)
            * <GKRQuotientComputation as SumcheckComputation<EF>>::eval_extension(
                &Default::default(),
                &[next_num_left, next_num_right, next_den_left, next_den_right],
                &[alpha],
            )
    {
        return Err(ProofError::InvalidProof);
    }

    let beta = verifier_state.sample();
    let next_claim_num = next_num_left * (EF::ONE - beta) + next_num_right * beta;
    let next_claim_den = next_den_left * (EF::ONE - beta) + next_den_right * beta;
    let mut next_claim_point = postponed.point.clone();
    next_claim_point.0.insert(0, beta);

    Ok((next_claim_point, next_claim_num, next_claim_den))
}

fn sum_quotients_2_by_2<F: PrimeCharacteristicRing + Sync + Send + Copy>(
    numerators: &[F],
    denominators: &[F],
) -> Vec<Vec<F>> {
    let n = numerators.len();
    let mut new_numerators = unsafe { uninitialized_vec(n / 2) };
    let mut new_denominators = unsafe { uninitialized_vec(n / 2) };
    let n_over_2 = n / 2;
    new_numerators
        .par_iter_mut()
        .zip(new_denominators.par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            let prev_num_1 = numerators[i];
            let prev_num_2 = numerators[n_over_2 + i];
            let prev_den_1 = denominators[i];
            let prev_den_2 = denominators[n_over_2 + i];
            *num = prev_num_1 * prev_den_2 + prev_num_2 * prev_den_1;
            *den = prev_den_1 * prev_den_2;
        });
    vec![new_numerators, new_denominators]
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
        let _ = prove_gkr_quotient(
            &mut prover_state,
            &MleGroupRef::ExtensionPacked(vec![
                &pack_extension(&numerators),
                &pack_extension(&denominators),
            ]),
        );
        println!("Proving time: {:?}", time.elapsed());

        let mut verifier_state = build_verifier_state(&prover_state);

        let (retrieved_quotient, claim_point, claim_num, claim_den) =
            verify_gkr_quotient::<EF>(&mut verifier_state, log_n).unwrap();
        assert_eq!(retrieved_quotient, real_quotient);
        assert_eq!(numerators.evaluate(&claim_point), claim_num);
        assert_eq!(denominators.evaluate(&claim_point), claim_den);
    }
}
