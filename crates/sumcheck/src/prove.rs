use p3_field::ExtensionField;
use p3_field::PrimeCharacteristicRing;
use rayon::prelude::*;
use utils::pack_extension;
use utils::packing_log_width;
use utils::unpack_extension;
use utils::{FSProver, PF, univariate_selectors};
use whir_p3::fiat_shamir::FSChallenger;
use whir_p3::poly::dense::WhirDensePolynomial;
use whir_p3::poly::evals::eval_eq;
use whir_p3::poly::multilinear::MultilinearPoint;

use crate::MleGroup;
use crate::SumcheckComputation;
use crate::{Mle, MySumcheckComputation};

#[allow(clippy::too_many_arguments)]
pub fn prove<'a, EF, SC>(
    skips: usize, // skips == 1: classic sumcheck. skips >= 2: sumcheck with univariate skips (eprint 2024/108)
    multilinears: impl Into<MleGroup<'a, EF>>,
    computation: &SC,
    batching_scalars: &[EF],
    eq_factor: Option<(Vec<EF>, Option<Mle<EF>>)>, // (a, b, c ...), eq_poly(b, c, ...)
    is_zerofier: bool,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    sum: EF,
    missing_mul_factor: Option<EF>,
) -> (MultilinearPoint<EF>, Vec<EF>, EF)
where
    EF: ExtensionField<PF<EF>>,
    SC: MySumcheckComputation<EF>,
{
    let (challenges, mut final_folds, mut sum) = prove_in_parallel_1(
        vec![skips],
        vec![multilinears],
        vec![computation],
        vec![batching_scalars],
        vec![eq_factor],
        vec![is_zerofier],
        prover_state,
        vec![sum],
        vec![missing_mul_factor],
        true,
    );

    (challenges, final_folds.pop().unwrap(), sum.pop().unwrap())
}

#[allow(clippy::too_many_arguments)]
pub fn prove_in_parallel_1<'a, EF, SC, M: Into<MleGroup<'a, EF>>>(
    skips: Vec<usize>, // skips == 1: classic sumcheck. skips >= 2: sumcheck with univariate skips (eprint 2024/108)
    multilinears: Vec<M>,
    computations: Vec<&SC>,
    batching_scalars: Vec<&[EF]>,
    eq_factors: Vec<Option<(Vec<EF>, Option<Mle<EF>>)>>, // (a, b, c ...), eq_poly(b, c, ...)
    is_zerofier: Vec<bool>,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    sums: Vec<EF>,
    missing_mul_factors: Vec<Option<EF>>,
    share_initial_challenges: bool, // otherwise, share the final challenges
) -> (MultilinearPoint<EF>, Vec<Vec<EF>>, Vec<EF>)
where
    EF: ExtensionField<PF<EF>>,
    SC: MySumcheckComputation<EF>,
{
    prove_in_parallel_3::<EF, SC, SC, SC, M>(
        skips,
        multilinears,
        computations,
        vec![],
        vec![],
        batching_scalars,
        eq_factors,
        is_zerofier,
        prover_state,
        sums,
        missing_mul_factors,
        share_initial_challenges,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn prove_in_parallel_3<'a, EF, SC1, SC2, SC3, M: Into<MleGroup<'a, EF>>>(
    mut skips: Vec<usize>, // skips == 1: classic sumcheck. skips >= 2: sumcheck with univariate skips (eprint 2024/108)
    multilinears: Vec<M>,
    computations_1: Vec<&SC1>,
    computations_2: Vec<&SC2>,
    computations_3: Vec<&SC3>,
    batching_scalars: Vec<&[EF]>,
    mut eq_factors: Vec<Option<(Vec<EF>, Option<Mle<EF>>)>>, // (a, b, c ...), eq_poly(b, c, ...)
    mut is_zerofier: Vec<bool>,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    mut sums: Vec<EF>,
    mut missing_mul_factors: Vec<Option<EF>>,
    share_initial_challenges: bool, // otherwise, share the final challenges
) -> (MultilinearPoint<EF>, Vec<Vec<EF>>, Vec<EF>)
where
    EF: ExtensionField<PF<EF>>,
    SC1: MySumcheckComputation<EF>,
    SC2: MySumcheckComputation<EF>,
    SC3: MySumcheckComputation<EF>,
{
    let n_sumchecks = multilinears.len();
    assert_eq!(n_sumchecks, skips.len());
    assert_eq!(
        n_sumchecks,
        computations_1.len() + computations_2.len() + computations_3.len()
    );
    assert_eq!(n_sumchecks, batching_scalars.len());
    assert_eq!(n_sumchecks, eq_factors.len());
    assert_eq!(n_sumchecks, is_zerofier.len());
    assert_eq!(n_sumchecks, sums.len());
    assert_eq!(n_sumchecks, missing_mul_factors.len());

    let mut multilinears: Vec<MleGroup<'a, EF>> =
        multilinears.into_iter().map(Into::into).collect();
    let mut eq_factors: Vec<Option<(Vec<EF>, Mle<EF>)>> = (0..n_sumchecks)
        .map(|i| {
            eq_factors[i].take().map(|(eq_point, eq_mle)| {
                let eq_mle = eq_mle.unwrap_or_else(|| {
                    let eval_eq_ext = eval_eq(&eq_point[1..]);
                    if multilinears[i].by_ref().is_packed() {
                        Mle::ExtensionPacked(pack_extension(&eval_eq_ext))
                    } else {
                        Mle::Extension(eval_eq_ext)
                    }
                });
                (eq_point, eq_mle)
            })
        })
        .collect();
    let mut n_vars: Vec<usize> = multilinears.iter().map(|m| m.by_ref().n_vars()).collect();
    for i in 0..n_sumchecks {
        if let Some((eq_point, eq_mle)) = &eq_factors[i] {
            assert_eq!(eq_point.len(), n_vars[i] - skips[i] + 1);
            assert_eq!(eq_mle.n_vars(), eq_point.len() - 1);
            assert_eq!(eq_mle.is_packed(), multilinears[i].by_ref().is_packed());
        }
    }

    let n_rounds: Vec<usize> = (0..n_sumchecks).map(|i| n_vars[i] - skips[i] + 1).collect();
    let max_n_rounds = Iterator::max(n_rounds.iter()).copied().unwrap();

    let mut challenges = Vec::new();
    for round in 0..max_n_rounds {
        let concerned_sumchecks: Vec<usize> = if share_initial_challenges {
            (0..n_sumchecks).filter(|&i| n_rounds[i] > round).collect()
        } else {
            let remaining_rounds = max_n_rounds - round;
            (0..n_sumchecks)
                .filter(|&i| n_rounds[i] >= remaining_rounds)
                .collect()
        };
        // If Packing is enabled, and there are too little variables, we unpack everything:
        for &i in &concerned_sumchecks {
            if multilinears[i].by_ref().is_packed() {
                if n_vars[i] <= 1 + packing_log_width::<EF>() {
                    // unpack
                    multilinears[i] = multilinears[i].by_ref().unpack().into();
                    if let Some((_, eq_mle)) = &mut eq_factors[i] {
                        *eq_mle =
                            Mle::Extension(unpack_extension(eq_mle.as_extension_packed().unwrap()));
                    }
                }
            }
        }

        let mut ps = vec![WhirDensePolynomial::default(); n_sumchecks];
        for &i in &concerned_sumchecks {
            if i < computations_1.len() {
                ps[i] = compute_and_send_polynomial(
                    skips[i],
                    &multilinears[i],
                    computations_1[i],
                    &eq_factors[i],
                    batching_scalars[i],
                    is_zerofier[i],
                    prover_state,
                    sums[i],
                    missing_mul_factors[i],
                );
            } else if i < computations_1.len() + computations_2.len() {
                ps[i] = compute_and_send_polynomial(
                    skips[i],
                    &multilinears[i],
                    computations_2[i - computations_1.len()],
                    &eq_factors[i],
                    batching_scalars[i],
                    is_zerofier[i],
                    prover_state,
                    sums[i],
                    missing_mul_factors[i],
                );
            } else {
                ps[i] = compute_and_send_polynomial(
                    skips[i],
                    &multilinears[i],
                    computations_3[i - computations_1.len() - computations_2.len()],
                    &eq_factors[i],
                    batching_scalars[i],
                    is_zerofier[i],
                    prover_state,
                    sums[i],
                    missing_mul_factors[i],
                );
            }
        }

        let challenge = prover_state.sample();
        challenges.push(challenge);

        for &i in &concerned_sumchecks {
            on_challenge_received(
                skips[i],
                &mut multilinears[i],
                &mut n_vars[i],
                &mut eq_factors[i],
                &mut sums[i],
                &mut missing_mul_factors[i],
                challenge,
                &ps[i],
            );
            skips[i] = 1;
            is_zerofier[i] = false;
        }
    }

    let final_folds = (0..n_sumchecks)
        .map(|i| {
            multilinears[i]
                .by_ref()
                .as_extension()
                .unwrap()
                .into_iter()
                .map(|m| {
                    assert_eq!(m.len(), 1);
                    m[0]
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    (MultilinearPoint(challenges), final_folds, sums)
}

#[allow(clippy::too_many_arguments)]
fn compute_and_send_polynomial<'a, EF, SC>(
    skips: usize, // the first round will fold 2^skips (instead of 2 in the basic sumcheck)
    multilinears: &MleGroup<'a, EF>,
    computation: &SC,
    eq_factor: &Option<(Vec<EF>, Mle<EF>)>, // (a, b, c ...), eq_poly(b, c, ...)
    batching_scalars: &[EF],
    is_zerofier: bool,
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    sum: EF,
    missing_mul_factor: Option<EF>,
) -> WhirDensePolynomial<EF>
where
    EF: ExtensionField<PF<EF>>,
    SC: MySumcheckComputation<EF>,
{
    let selectors = univariate_selectors::<PF<EF>>(skips);

    let mut p_evals = Vec::<(PF<EF>, EF)>::new();
    let start = if is_zerofier {
        p_evals.extend((0..1 << skips).map(|i| (PF::<EF>::from_usize(i), EF::ZERO)));
        1 << skips
    } else {
        0
    };

    let computation_degree = SumcheckComputation::<EF, EF>::degree(computation);
    let zs = (start..=computation_degree * ((1 << skips) - 1))
        .filter(|&i| i != (1 << skips) - 1)
        .collect::<Vec<_>>();

    let folding_scalars = zs
        .iter()
        .map(|&z| {
            selectors
                .iter()
                .map(|s| s.evaluate(PF::<EF>::from_usize(z)))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<Vec<PF<EF>>>>();

    p_evals.extend(multilinears.by_ref().sumcheck_compute(
        &zs,
        skips,
        eq_factor.as_ref().map(|(_, eq_mle)| eq_mle),
        &folding_scalars,
        computation,
        batching_scalars,
        missing_mul_factor,
    ));

    if !is_zerofier {
        let missing_sum_z = if let Some((eq_factor, _)) = eq_factor {
            (sum - (0..(1 << skips) - 1)
                .map(|i| p_evals[i].1 * selectors[i].evaluate(eq_factor[0]))
                .sum::<EF>())
                / selectors[(1 << skips) - 1].evaluate(eq_factor[0])
        } else {
            sum - p_evals[..(1 << skips) - 1]
                .iter()
                .map(|(_, s)| *s)
                .sum::<EF>()
        };
        p_evals.push((PF::<EF>::from_usize((1 << skips) - 1), missing_sum_z));
    }

    let mut p = WhirDensePolynomial::lagrange_interpolation(&p_evals).unwrap();

    if let Some((eq_factor, _)) = &eq_factor {
        // https://eprint.iacr.org/2024/108.pdf Section 3.2
        // We do not take advantage of this trick to send less data, but we could do so in the future (TODO)
        p *= &WhirDensePolynomial::lagrange_interpolation(
            &(0..1 << skips)
                .into_par_iter()
                .map(|i| (PF::<EF>::from_usize(i), selectors[i].evaluate(eq_factor[0])))
                .collect::<Vec<_>>(),
        )
        .unwrap();
    }
    // sanity check
    assert_eq!(
        (0..1 << skips)
            .map(|i| p.evaluate(EF::from_usize(i)))
            .sum::<EF>(),
        sum
    );

    prover_state.add_extension_scalars(&p.coeffs);

    p
}

#[allow(clippy::too_many_arguments)]
fn on_challenge_received<'a, EF>(
    skips: usize, // the first round will fold 2^skips (instead of 2 in the basic sumcheck)
    multilinears: &mut MleGroup<'a, EF>,
    n_vars: &mut usize,
    eq_factor: &mut Option<(Vec<EF>, Mle<EF>)>, // (a, b, c ...), eq_poly(b, c, ...)
    sum: &mut EF,
    missing_mul_factor: &mut Option<EF>,
    challenge: EF,
    p: &WhirDensePolynomial<EF>,
) where
    EF: ExtensionField<PF<EF>>,
{
    *sum = p.evaluate(challenge);
    *n_vars -= skips;

    let selectors = univariate_selectors::<PF<EF>>(skips);

    let folding_scalars = selectors
        .iter()
        .map(|s| s.evaluate(challenge))
        .collect::<Vec<_>>();
    if let Some((eq_factor, eq_mle)) = eq_factor {
        *missing_mul_factor = Some(
            selectors
                .iter()
                .map(|s| s.evaluate(eq_factor[0]) * s.evaluate(challenge))
                .sum::<EF>()
                * missing_mul_factor.unwrap_or(EF::ONE)
                / (EF::ONE - eq_factor.get(1).copied().unwrap_or_default()),
        );
        eq_factor.remove(0);
        eq_mle.truncate(eq_mle.packed_len() / 2);
    }

    *multilinears = multilinears
        .by_ref()
        .fold_in_large_field(&folding_scalars)
        .into()
}
