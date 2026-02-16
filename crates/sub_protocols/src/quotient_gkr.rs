use multilinear_toolkit::prelude::*;
use tracing::instrument;

use crate::MIN_VARS_FOR_PACKING;

/*
GKR to compute sum of fractions.
*/

#[instrument(skip_all)]
pub fn prove_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    numerators: &MleRef<'_, EF>,
    denominators: &MleRef<'_, EF>,
) -> (EF, MultilinearPoint<EF>, EF, EF) {
    assert!(numerators.is_packed() == denominators.is_packed());
    let mut layers: Vec<(Mle<'_, EF>, Mle<'_, EF>)> =
        vec![(numerators.soft_clone().into(), denominators.soft_clone().into())];

    loop {
        let (mut prev_numerators, mut prev_denominators) = layers.last().cloned().unwrap();
        if prev_numerators.is_packed() && prev_numerators.n_vars() < MIN_VARS_FOR_PACKING {
            (prev_numerators, prev_denominators) = (
                prev_numerators.unpack().as_owned_or_clone().into(),
                prev_denominators.unpack().as_owned_or_clone().into(),
            )
        }
        if prev_numerators.n_vars() == 1 {
            break;
        }
        let (new_numerators, new_denominators) = sum_quotients(prev_numerators.by_ref(), prev_denominators.by_ref());
        layers.push((new_numerators.into(), new_denominators.into()));
    }

    let (last_numerators, last_denominators) = layers.pop().unwrap();
    let last_numerators = last_numerators.as_owned().unwrap();
    let last_numerators = last_numerators.as_extension().unwrap();
    let last_denominators = last_denominators.as_owned().unwrap();
    let last_denominators = last_denominators.as_extension().unwrap();
    prover_state.add_extension_scalars(last_numerators);
    prover_state.add_extension_scalars(last_denominators);
    let quotient = last_numerators[0] / last_denominators[0] + last_numerators[1] / last_denominators[1];

    let mut point = MultilinearPoint(vec![prover_state.sample()]);
    let mut claims = vec![last_numerators.evaluate(&point), last_denominators.evaluate(&point)];

    for (nums, denoms) in layers.iter().rev() {
        (point, claims) = prove_gkr_quotient_step(prover_state, nums, denoms, &point, claims);
    }
    assert_eq!(claims.len(), 2);
    (quotient, point, claims[0], claims[1])
}

fn prove_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    numerators: &Mle<'_, EF>,
    denominators: &Mle<'_, EF>,
    claim_point: &MultilinearPoint<EF>,
    claims: Vec<EF>,
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let prev_numerators_and_denominators_split = match (numerators.by_ref(), denominators.by_ref()) {
        (MleRef::ExtensionPacked(numerators), MleRef::ExtensionPacked(denominators)) => {
            let (left_nums, right_nums) = numerators.split_at(numerators.len() / 2);
            let (left_dens, right_dens) = denominators.split_at(denominators.len() / 2);
            MleGroupRef::ExtensionPacked(vec![left_nums, right_nums, left_dens, right_dens])
        }
        (MleRef::Extension(numerators), MleRef::Extension(denominators)) => {
            let (left_nums, right_nums) = numerators.split_at(numerators.len() / 2);
            let (left_dens, right_dens) = denominators.split_at(denominators.len() / 2);
            MleGroupRef::Extension(vec![left_nums, right_nums, left_dens, right_dens])
        }
        _ => unreachable!(),
    };

    let alpha = prover_state.sample();

    let (mut next_point, inner_evals, _) = sumcheck_prove::<EF, _, _>(
        1,
        prev_numerators_and_denominators_split,
        None,
        &GKRQuotientComputation::<2> {},
        &alpha.powers().take(2).collect(),
        Some((claim_point.0.clone(), None)),
        false,
        prover_state,
        dot_product(claims.iter().copied(), alpha.powers()),
        false,
    );

    prover_state.add_extension_scalars(&inner_evals);
    let beta = prover_state.sample();

    let next_claims = inner_evals
        .chunks_exact(2)
        .map(|chunk| chunk.evaluate(&MultilinearPoint(vec![beta])))
        .collect::<Vec<_>>();

    next_point.0.insert(0, beta);

    (next_point, next_claims)
}

pub fn verify_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
) -> Result<(EF, MultilinearPoint<EF>, EF, EF), ProofError> {
    let last_nums = verifier_state.next_extension_scalars_vec(2)?;
    let last_dens = verifier_state.next_extension_scalars_vec(2)?;

    let quotient = last_nums[0] / last_dens[0] + last_nums[1] / last_dens[1];

    let mut point = MultilinearPoint(vec![verifier_state.sample()]);
    let mut claims_num = last_nums.evaluate(&point);
    let mut claims_den = last_dens.evaluate(&point);
    for i in 1..n_vars {
        (point, claims_num, claims_den) = verify_gkr_quotient_step(verifier_state, i, &point, claims_num, claims_den)?;
    }

    Ok((quotient, point, claims_num, claims_den))
}

fn verify_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
    point: &MultilinearPoint<EF>,
    claims_num: EF,
    claims_den: EF,
) -> Result<(MultilinearPoint<EF>, EF, EF), ProofError> {
    let alpha = verifier_state.sample();

    let (retrieved_quotient, postponed) = sumcheck_verify(verifier_state, n_vars, 3)?;

    if retrieved_quotient != claims_num + alpha * claims_den {
        return Err(ProofError::InvalidProof);
    }

    let inner_evals = verifier_state.next_extension_scalars_vec(4)?;

    if postponed.value
        != point.eq_poly_outside(&postponed.point)
            * <GKRQuotientComputation<2> as SumcheckComputation<EF>>::eval_extension(
                &Default::default(),
                &inner_evals,
                &[],
                &alpha.powers().take(2).collect(),
            )
    {
        return Err(ProofError::InvalidProof);
    }

    let beta = verifier_state.sample();

    let next_claims_numerators = (&inner_evals[..2]).evaluate(&MultilinearPoint(vec![beta]));
    let next_claims_denominators = (&inner_evals[2..]).evaluate(&MultilinearPoint(vec![beta]));
    let mut next_point = postponed.point.clone();
    next_point.0.insert(0, beta);

    Ok((next_point, next_claims_numerators, next_claims_denominators))
}

fn sum_quotients<EF: ExtensionField<PF<EF>>>(
    numerators: MleRef<'_, EF>,
    denominators: MleRef<'_, EF>,
) -> (MleOwned<EF>, MleOwned<EF>) {
    match (numerators, denominators) {
        (MleRef::ExtensionPacked(numerators), MleRef::ExtensionPacked(denominators)) => {
            let (new_numerators, new_denominators) = sum_quotients_2_by_2(numerators, denominators);
            (
                MleOwned::ExtensionPacked(new_numerators),
                MleOwned::ExtensionPacked(new_denominators),
            )
        }
        (MleRef::Extension(numerators), MleRef::Extension(denominators)) => {
            let (new_numerators, new_denominators) = sum_quotients_2_by_2(numerators, denominators);
            (
                MleOwned::Extension(new_numerators),
                MleOwned::Extension(new_denominators),
            )
        }
        _ => unreachable!(),
    }
}
fn sum_quotients_2_by_2<F: PrimeCharacteristicRing + Sync + Send + Copy>(
    numerators: &[F],
    denominators: &[F],
) -> (Vec<F>, Vec<F>) {
    let n = numerators.len();
    let new_n = n / 2;
    let mut new_numerators = unsafe { uninitialized_vec(new_n) };
    let mut new_denominators = unsafe { uninitialized_vec(new_n) };
    new_numerators
        .par_iter_mut()
        .zip(new_denominators.par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            let my_numerators: [_; 2] = [numerators[i], numerators[i + new_n]];
            let my_denominators: [_; 2] = [denominators[i], denominators[i + new_n]];
            *num = my_numerators[0] * my_denominators[1] + my_numerators[1] * my_denominators[0];
            *den = my_denominators[0] * my_denominators[1];
        });
    (new_numerators, new_denominators)
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use utils::{build_prover_state, build_verifier_state, init_tracing};

    type EF = QuinticExtensionFieldKB;

    fn sum_all_quotients(nums: &[EF], den: &[EF]) -> EF {
        nums.iter().zip(den.iter()).map(|(&n, &d)| n / d).sum()
    }

    const N_GROUPS: usize = 2;

    #[test]
    fn test_gkr_quotient() {
        let log_n = 13;
        let n = 1 << log_n;
        init_tracing();

        let mut rng = StdRng::seed_from_u64(0);

        let numerators = (0..n).map(|_| rng.random()).collect::<Vec<EF>>();
        let c: EF = rng.random();
        let denominators_indexes = (0..n)
            .map(|_| PF::<EF>::from_usize(rng.random_range(..n)))
            .collect::<Vec<_>>();
        let denominators = denominators_indexes.iter().map(|&i| c - i).collect::<Vec<EF>>();
        let real_quotient = sum_all_quotients(&numerators, &denominators);
        let mut prover_state = build_prover_state();

        let time = Instant::now();
        let prover_statements = prove_gkr_quotient::<EF>(
            &mut prover_state,
            &MleRef::ExtensionPacked(&pack_extension(&numerators)),
            &MleRef::ExtensionPacked(&pack_extension(&denominators)),
        );
        println!("Proving time: {:?}", time.elapsed());

        let mut verifier_state = build_verifier_state(prover_state);

        let verifier_statements = verify_gkr_quotient::<EF>(&mut verifier_state, log_n).unwrap();
        assert_eq!(&verifier_statements, &prover_statements);
        let (retrieved_quotient, claim_point, claim_num, claim_den) = verifier_statements;

        assert_eq!(retrieved_quotient, real_quotient);
        assert_eq!(numerators.evaluate(&claim_point), claim_num);
        assert_eq!(denominators.evaluate(&claim_point), claim_den);
    }
}
