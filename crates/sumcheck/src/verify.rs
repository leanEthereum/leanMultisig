use p3_field::ExtensionField;
use utils::{FSVerifier, PF};
use whir_p3::{
    fiat_shamir::{FSChallenger, errors::ProofError},
    poly::{dense::DensePolynomial, multilinear::Evaluation},
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

fn verify_core<EF>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    max_degree_per_vars: Vec<usize>,
    sumation_sets: Vec<Vec<EF>>,
) -> Result<(EF, Evaluation<EF>), ProofError>
where
    EF: ExtensionField<PF<EF>>,
{
    let n_sumchecks = max_degree_per_vars.len();
    assert_eq!(n_sumchecks, sumation_sets.len(),);

    let mut challenges = Vec::new();
    let mut first_round = true;
    let (mut sum, mut target) = (EF::ZERO, EF::ZERO);

    let n_vars = max_degree_per_vars.len();

    for var in 0..n_vars {
        let deg = max_degree_per_vars[var];
        let sumation_set = &sumation_sets[var];
        let coeffs = verifier_state.next_extension_scalars_vec(deg + 1)?;
        let pol = DensePolynomial::new(coeffs);
        let computed_sum = sumation_set.iter().map(|&s| pol.evaluate(s)).sum();
        if first_round {
            first_round = false;
            sum = computed_sum;
        } else if target != computed_sum {
            return Err(ProofError::InvalidProof);
        }
        let challenge = verifier_state.sample();
        challenges.push(challenge);

        target = pol.evaluate(challenge);
    }

    Ok((sum, Evaluation::new(challenges, target)))
}
