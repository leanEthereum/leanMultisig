use std::ops::Mul;

use backend::*;

use crate::{MIN_VARS_FOR_PACKING, N_VARS_TO_SEND_GKR_COEFFS};

/*
GKR to compute sum of fractions.
*/

pub fn prove_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    numerators: &MleRef<'_, EF>,
    denominators: &MleRef<'_, EF>,
) -> (EF, MultilinearPoint<EF>, EF, EF) {
    assert!(numerators.n_vars() == denominators.n_vars());
    assert!(numerators.n_vars() > N_VARS_TO_SEND_GKR_COEFFS);
    assert!(numerators.is_packed() == denominators.is_packed());
    let mut layers: Vec<(Mle<'_, EF>, Mle<'_, EF>)> =
        vec![(numerators.soft_clone().into(), denominators.soft_clone().into())];

    loop {
        let mut prev_numerators: Mle<'_, _> = layers.last().unwrap().0.by_ref().soft_clone().into();
        let mut prev_denominators: Mle<'_, _> = layers.last().unwrap().1.by_ref().soft_clone().into();
        if prev_numerators.is_packed() && prev_numerators.n_vars() < MIN_VARS_FOR_PACKING {
            (prev_numerators, prev_denominators) = (
                prev_numerators.unpack().as_owned_or_clone().into(),
                prev_denominators.unpack().as_owned_or_clone().into(),
            )
        }
        if prev_numerators.n_vars() <= N_VARS_TO_SEND_GKR_COEFFS {
            break;
        }
        let (new_numerators, new_denominators) = sum_quotients(prev_numerators.by_ref(), prev_denominators.by_ref());
        layers.push((new_numerators.into(), new_denominators.into()));
    }

    let (last_numerators_mle, last_denominators_mle) = layers.pop().unwrap();
    let last_numerators_owned = last_numerators_mle.unpack().as_owned_or_clone();
    let last_denominators_owned = last_denominators_mle.unpack().as_owned_or_clone();
    let last_numerators = last_numerators_owned.as_extension().unwrap();
    let last_denominators = last_denominators_owned.as_extension().unwrap();
    prover_state.add_extension_scalars(last_numerators);
    prover_state.add_extension_scalars(last_denominators);
    let quotient = compute_quotient(last_numerators, last_denominators);

    let mut point = MultilinearPoint(prover_state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS));
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
    let alpha = prover_state.sample();
    assert_eq!(claims.len(), 2);
    let sum = claims[0] + claims[1] * alpha;
    let extra_data: Vec<EF> = alpha.powers().take(2).collect();

    let (mut next_point, inner_evals) = match (numerators.by_ref(), denominators.by_ref()) {
        (MleRef::BasePacked(nums), MleRef::ExtensionPacked(dens)) => {
            prove_gkr_quotient_step_base_ext(prover_state, nums, dens, claim_point, &extra_data, sum)
        }
        _ => {
            let ext_nums_unpacked: Vec<EF>;
            let group = match (numerators.by_ref(), denominators.by_ref()) {
                (MleRef::ExtensionPacked(numerators), MleRef::ExtensionPacked(denominators)) => {
                    let (ln, rn) = numerators.split_at(numerators.len() / 2);
                    let (ld, rd) = denominators.split_at(denominators.len() / 2);
                    MleGroupRef::ExtensionPacked(vec![ln, rn, ld, rd])
                }
                (MleRef::Extension(numerators), MleRef::Extension(denominators)) => {
                    let (ln, rn) = numerators.split_at(numerators.len() / 2);
                    let (ld, rd) = denominators.split_at(denominators.len() / 2);
                    MleGroupRef::Extension(vec![ln, rn, ld, rd])
                }
                (MleRef::Base(numerators), MleRef::Extension(denominators)) => {
                    ext_nums_unpacked = numerators.iter().map(|&x| EF::from(x)).collect();
                    let (ln, rn) = ext_nums_unpacked.split_at(ext_nums_unpacked.len() / 2);
                    let (ld, rd) = denominators.split_at(denominators.len() / 2);
                    MleGroupRef::Extension(vec![ln, rn, ld, rd])
                }
                _ => unreachable!(),
            };
            let (point, evals, _) = sumcheck_prove::<EF, _, _>(
                group,
                &GKRQuotientComputation {},
                &extra_data,
                Some(claim_point.0.clone()),
                prover_state,
                sum,
                false,
            );
            (point, evals)
        }
    };

    prover_state.add_extension_scalars(&inner_evals);
    let beta = prover_state.sample();

    let next_claims = inner_evals
        .chunks_exact(2)
        .map(|chunk| chunk.evaluate(&MultilinearPoint(vec![beta])))
        .collect::<Vec<_>>();

    next_point.0.insert(0, beta);

    (next_point, next_claims)
}

fn prove_gkr_quotient_step_base_ext<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    nums: &[PFPacking<EF>],
    dens: &[EFPacking<EF>],
    claim_point: &MultilinearPoint<EF>,
    extra_data: &[EF],
    sum: EF,
) -> (MultilinearPoint<EF>, Vec<EF>) {
    let eq_point = &claim_point.0;
    let n_vars = eq_point.len();
    let alpha = extra_data[1];

    let half = nums.len() / 2;
    let (nl, nr) = nums.split_at(half);
    let (dl, dr) = dens.split_at(half);

    let mut split_eq = SplitEq::new(&eq_point[1..]);
    let poly_0 =
        compute_gkr_quotient_sumcheck_polynomial_split_eq(nl, nr, dl, dr, alpha, eq_point[0], &split_eq, EF::ONE, sum);
    prover_state.add_sumcheck_polynomial(&poly_0.coeffs, Some(eq_point[0]));
    let challenge_0 = prover_state.sample();

    let eq_eval_0 = (EF::ONE - eq_point[0]) * (EF::ONE - challenge_0) + eq_point[0] * challenge_0;
    let sum_1 = poly_0.evaluate(challenge_0) * eq_eval_0;
    let mmf_1 = eq_eval_0 / (EF::ONE - eq_point.get(1).copied().unwrap_or_default());

    split_eq.truncate_half();
    let r = challenge_0;
    let r_packed = EFPacking::<EF>::from(r);
    let fold_base = |u: &[PFPacking<EF>], i: usize, half: usize, quarter: usize| {
        let left = r_packed * (u[i + half] - u[i]) + u[i];
        let right = r_packed * (u[i + half + quarter] - u[i + quarter]) + u[i + quarter];
        (left, right)
    };
    let fold_ext = |u: &[EFPacking<EF>], i: usize, half: usize, quarter: usize| {
        let left = (u[i + half] - u[i]) * r + u[i];
        let right = (u[i + half + quarter] - u[i + quarter]) * r + u[i + quarter];
        (left, right)
    };
    let (poly_1, folded) = fold_and_compute_gkr_quotient_split_eq(
        nl,
        nr,
        dl,
        dr,
        fold_base,
        fold_ext,
        alpha,
        eq_point[1],
        &split_eq,
        mmf_1,
        sum_1,
    );
    prover_state.add_sumcheck_polynomial(&poly_1.coeffs, Some(eq_point[1]));
    let challenge_1 = prover_state.sample();

    let eq_eval_1 = (EF::ONE - eq_point[1]) * (EF::ONE - challenge_1) + eq_point[1] * challenge_1;
    let sum_2 = poly_1.evaluate(challenge_1) * eq_eval_1;
    let mmf_2 = eq_eval_0 * eq_eval_1;

    let group = MleGroupOwned::ExtensionPacked(folded);

    let (remaining_point, final_group, _) = sumcheck_prove_many_rounds(
        group,
        Some(challenge_1),
        &GKRQuotientComputation {},
        &extra_data.to_vec(),
        Some(eq_point[2..].to_vec()),
        prover_state,
        sum_2,
        Some(mmf_2),
        n_vars - 2,
        false,
        0,
    );

    let final_group = final_group.by_ref().unpack().as_owned_or_clone();
    let final_folds = final_group.as_extension().unwrap();
    let inner_evals: Vec<EF> = final_folds
        .iter()
        .map(|m| {
            assert_eq!(m.len(), 1);
            m[0]
        })
        .collect();

    let mut point = MultilinearPoint(vec![challenge_0, challenge_1]);
    point.0.extend(remaining_point.0);
    (point, inner_evals)
}

pub fn verify_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
) -> Result<(EF, MultilinearPoint<EF>, EF, EF), ProofError> {
    assert!(n_vars > N_VARS_TO_SEND_GKR_COEFFS);
    let send_len = 1 << N_VARS_TO_SEND_GKR_COEFFS;
    let last_nums = verifier_state.next_extension_scalars_vec(send_len)?;
    let last_dens = verifier_state.next_extension_scalars_vec(send_len)?;
    let quotient: EF = compute_quotient(&last_nums, &last_dens);
    let mut point = MultilinearPoint(verifier_state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS));
    let mut claims_num = last_nums.evaluate(&point);
    let mut claims_den = last_dens.evaluate(&point);
    for i in N_VARS_TO_SEND_GKR_COEFFS..n_vars {
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
    let expected_sum = claims_num + alpha * claims_den;
    let postponed = sumcheck_verify(verifier_state, n_vars, 3, expected_sum, Some(&point.0))?;
    let inner_evals = verifier_state.next_extension_scalars_vec(4)?;
    if postponed.value
        != point.eq_poly_outside(&postponed.point)
            * GKRQuotientComputation::eval_extension(
                &Default::default(),
                &inner_evals,
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
        (MleRef::ExtensionPacked(n), MleRef::ExtensionPacked(d)) => {
            let (nn, nd) = sum_quotients_2_by_2(n, d);
            (MleOwned::ExtensionPacked(nn), MleOwned::ExtensionPacked(nd))
        }
        (MleRef::Extension(n), MleRef::Extension(d)) => {
            let (nn, nd) = sum_quotients_2_by_2(n, d);
            (MleOwned::Extension(nn), MleOwned::Extension(nd))
        }
        (MleRef::BasePacked(n), MleRef::ExtensionPacked(d)) => {
            let (nn, nd) = sum_quotients_2_by_2(n, d);
            (MleOwned::ExtensionPacked(nn), MleOwned::ExtensionPacked(nd))
        }
        _ => unreachable!(),
    }
}

fn sum_quotients_2_by_2<N, D>(numerators: &[N], denominators: &[D]) -> (Vec<D>, Vec<D>)
where
    N: Copy + Sync + Send,
    D: PrimeCharacteristicRing + Sync + Send + Copy + Mul<N, Output = D>,
{
    let n = numerators.len();
    assert_eq!(n, denominators.len());
    let new_n = n / 2;
    let mut new_numerators = unsafe { uninitialized_vec(new_n) };
    let mut new_denominators = unsafe { uninitialized_vec(new_n) };
    new_numerators
        .par_iter_mut()
        .zip(new_denominators.par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            *num = denominators[i + new_n] * numerators[i] + denominators[i] * numerators[i + new_n];
            *den = denominators[i] * denominators[i + new_n];
        });
    (new_numerators, new_denominators)
}

fn compute_quotient<EF: ExtensionField<PF<EF>>>(numerators: &[EF], denominators: &[EF]) -> EF {
    numerators.iter().zip(denominators).map(|(&n, &d)| n / d).sum()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{RngExt, SeedableRng, rngs::StdRng};
    use std::time::Instant;
    use utils::{build_prover_state, build_verifier_state, init_tracing};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    fn sum_all_quotients(nums: &[F], den: &[EF]) -> EF {
        nums.par_iter().zip(den).map(|(&n, &d)| EF::from(n) / d).sum()
    }

    #[test]
    fn test_gkr_quotient() {
        let log_n = 13;
        let n = 1 << log_n;
        init_tracing();

        let mut rng = StdRng::seed_from_u64(0);
        let numerators = (0..n).map(|_| rng.random()).collect::<Vec<F>>();
        let c: EF = rng.random();
        let denominators_indexes = (0..n)
            .map(|_| PF::<EF>::from_usize(rng.random_range(..n)))
            .collect::<Vec<_>>();
        let denominators = denominators_indexes.iter().map(|&i| c - i).collect::<Vec<EF>>();
        let real_quotient = sum_all_quotients(&numerators, &denominators);
        let mut prover_state = build_prover_state();

        let numerators = MleOwned::BasePacked(pack_extension(&numerators));
        let denominators = MleOwned::ExtensionPacked(pack_extension(&denominators));

        let time = Instant::now();
        let prover_statements =
            prove_gkr_quotient::<EF>(&mut prover_state, &numerators.by_ref(), &denominators.by_ref());
        println!("Proving time: {:?}", time.elapsed());

        let mut verifier_state = build_verifier_state(prover_state).unwrap();
        let verifier_statements = verify_gkr_quotient::<EF>(&mut verifier_state, log_n).unwrap();
        assert_eq!(&verifier_statements, &prover_statements);
        let (retrieved_quotient, claim_point, claim_num, claim_den) = verifier_statements;
        assert_eq!(retrieved_quotient, real_quotient);
        assert_eq!(numerators.evaluate(&claim_point), claim_num);
        assert_eq!(denominators.evaluate(&claim_point), claim_den);
    }
}
