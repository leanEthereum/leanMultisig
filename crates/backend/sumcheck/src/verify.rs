use fiat_shamir::*;
use field::*;
use poly::*;

pub fn sumcheck_verify<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
    degree: usize,
    expected_sum: EF,
    eq_alphas: Option<&[EF]>,
) -> Result<Evaluation<EF>, ProofError> {
    let mut target = expected_sum;
    let mut challenges = Vec::with_capacity(n_vars);

    for round in 0..n_vars {
        let eq_alpha = eq_alphas.map(|a| a[round]);
        let coeffs = verifier_state.next_sumcheck_polynomial(degree + 1, target, eq_alpha)?;
        let pol = DensePolynomial::new(coeffs);

        let challenge = verifier_state.sample();
        challenges.push(challenge);

        target = pol.evaluate(challenge);
    }

    Ok(Evaluation::new(challenges, target))
}
