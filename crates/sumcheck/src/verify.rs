use p3_field::ExtensionField;
use utils::{Evaluation, FSVerifier, PF};
use whir_p3::{
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::{dense::WhirDensePolynomial, multilinear::MultilinearPoint},
};

pub fn verify<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_vars: usize,
    degree: usize,
) -> Result<(EF, Evaluation<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
{
    let sumation_sets = vec![vec![EF::ZERO, EF::ONE]; n_vars];
    let max_degree_per_vars = vec![degree; n_vars];
    verify_core(verifier_state, max_degree_per_vars, sumation_sets)
}

pub fn verify_in_parallel<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_vars: &[usize],
    degrees: &[usize],
    share_initial_challenges: bool,
) -> Result<(Vec<EF>, MultilinearPoint<EF>, Vec<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
{
    verify_with_univariate_skip_in_parallel(
        verifier_state,
        1,
        n_vars,
        degrees,
        share_initial_challenges,
    )
}

pub fn verify_with_custom_degree_at_first_round<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    n_vars: usize,
    intial_degree: usize,
    remaining_degree: usize,
) -> Result<(EF, Evaluation<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
{
    let sumation_sets = vec![vec![EF::ZERO, EF::ONE]; n_vars];
    let mut max_degree_per_vars = vec![intial_degree; 1];
    max_degree_per_vars.extend(vec![remaining_degree; n_vars - 1]);
    verify_core(verifier_state, max_degree_per_vars, sumation_sets)
}

pub fn verify_with_univariate_skip<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    degree: usize,
    n_vars: usize,
    skips: usize,
) -> Result<(EF, Evaluation<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
{
    let mut max_degree_per_vars = vec![degree * ((1 << skips) - 1)];
    max_degree_per_vars.extend(vec![degree; n_vars - skips]);
    let mut sumation_sets = vec![(0..1 << skips).map(EF::from_usize).collect::<Vec<_>>()];
    sumation_sets.extend(vec![vec![EF::ZERO, EF::ONE]; n_vars - skips]);
    verify_core(verifier_state, max_degree_per_vars, sumation_sets)
}

pub fn verify_with_univariate_skip_in_parallel<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    skips: usize,
    n_vars: &[usize],
    degrees: &[usize],
    share_initial_challenges: bool,
) -> Result<(Vec<EF>, MultilinearPoint<EF>, Vec<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
{
    let n_sumchecks = n_vars.len();
    assert_eq!(n_sumchecks, degrees.len(),);
    let sumation_sets = (0..n_sumchecks)
        .map(|i| {
            [
                vec![(0..1 << skips).map(EF::from_usize).collect::<Vec<_>>()],
                vec![vec![EF::ZERO, EF::ONE]; n_vars[i] - skips],
            ]
            .concat()
        })
        .collect::<Vec<_>>();
    let max_degree_per_vars = (0..n_sumchecks)
        .map(|i| {
            [
                vec![degrees[i] * ((1 << skips) - 1)],
                vec![degrees[i]; n_vars[i] - skips],
            ]
            .concat()
        })
        .collect::<Vec<_>>();

    verify_core_in_parallel(
        verifier_state,
        max_degree_per_vars,
        sumation_sets,
        share_initial_challenges,
    )
}

fn verify_core<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    max_degree_per_vars: Vec<usize>,
    sumation_sets: Vec<Vec<EF>>,
) -> Result<(EF, Evaluation<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
{
    let (sum, challenge_point, challenge_value) = verify_core_in_parallel(
        verifier_state,
        vec![max_degree_per_vars],
        vec![sumation_sets],
        true,
    )?;
    Ok((
        sum[0],
        Evaluation {
            point: challenge_point,
            value: challenge_value[0],
        },
    ))
}

fn verify_core_in_parallel<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    max_degree_per_vars: Vec<Vec<usize>>,
    sumation_sets: Vec<Vec<Vec<EF>>>,
    share_initial_challenges: bool, // otherwise, share the final challenges
) -> Result<(Vec<EF>, MultilinearPoint<EF>, Vec<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
{
    let n_sumchecks = max_degree_per_vars.len();
    assert_eq!(n_sumchecks, sumation_sets.len(),);

    for i in 0..n_sumchecks {
        assert_eq!(max_degree_per_vars[i].len(), sumation_sets[i].len(),);
    }
    let mut challenges = Vec::new();
    let mut first_rounds = vec![true; n_sumchecks];
    let (mut sums, mut targets) = (vec![EF::ZERO; n_sumchecks], vec![EF::ZERO; n_sumchecks]);

    let n_vars = max_degree_per_vars
        .iter()
        .map(|v| v.len())
        .collect::<Vec<_>>();
    let max_n_vars = Iterator::max(n_vars.iter().copied()).unwrap();

    for var in 0..max_n_vars {
        let remaining_vars = max_n_vars - var;
        let concerned_sumchecks: Vec<usize> = if share_initial_challenges {
            (0..n_sumchecks).filter(|&i| n_vars[i] > var).collect()
        } else {
            (0..n_sumchecks)
                .filter(|&i| n_vars[i] >= remaining_vars)
                .collect()
        };
        let mut pols = vec![WhirDensePolynomial::default(); n_sumchecks];
        for &i in &concerned_sumchecks {
            let local_var = if share_initial_challenges {
                var
            } else {
                n_vars[i] - remaining_vars
            };
            let deg = max_degree_per_vars[i][local_var];
            let sumation_set = &sumation_sets[i][local_var];
            let coeffs = verifier_state.next_extension_scalars_vec(deg + 1)?;
            pols[i] = WhirDensePolynomial::from_coefficients_vec(coeffs);
            let computed_sum = sumation_set.iter().map(|&s| pols[i].evaluate(s)).sum();
            if first_rounds[i] {
                first_rounds[i] = false;
                sums[i] = computed_sum;
            } else if targets[i] != computed_sum {
                return Err(ProofError::InvalidProof);
            }
        }

        let challenge = verifier_state.sample();
        challenges.push(challenge);

        for &i in &concerned_sumchecks {
            targets[i] = pols[i].evaluate(challenge);
        }
    }

    Ok((sums, MultilinearPoint(challenges), targets))
}
