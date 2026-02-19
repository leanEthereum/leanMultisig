use fiat_shamir::*;
use field::*;
use poly::*;

pub fn sumcheck_verify<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
    degree: usize,
) -> Result<(EF, Evaluation<EF>), ProofError> {
    let sumation_sets = vec![vec![EF::ZERO, EF::ONE]; n_vars];
    let max_degree_per_vars = vec![degree; n_vars];
    verify_core(verifier_state, max_degree_per_vars, sumation_sets)
}

fn verify_core<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    max_degree_per_vars: Vec<usize>,
    sumation_sets: Vec<Vec<EF>>,
) -> Result<(EF, Evaluation<EF>), ProofError> {
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
