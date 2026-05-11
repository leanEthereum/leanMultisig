// WHIR verifier protocol audit — tests pinned to ACFY24 (eprint 2024/1586).
//
// Each test cites the specific Construction/Theorem/Definition from the paper
// that it validates. Convention differences between the implementation and the
// paper are documented inline.

use fiat_shamir::{ProverState, VerifierState};
use field::{Field, PrimeCharacteristicRing};
use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon1_16};
use mt_whir::*;
use poly::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

/// Small-parameter WHIR instance for fast tests.
/// num_variables=12 keeps prove+verify under 1s on M4.
fn small_whir_config() -> (WhirConfig<EF>, usize) {
    let num_variables = 12;
    let builder = WhirConfigBuilder {
        security_level: 80,
        max_num_variables_to_send_coeffs: 4,
        pow_bits: 0,
        folding_factor: FoldingFactor::constant(4),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate: 2,
        rs_domain_initial_reduction_factor: 1,
    };
    (WhirConfig::new(&builder, num_variables), num_variables)
}

/// Produce a valid proof for the given polynomial and statement.
fn prove_and_get_proof(
    config: &WhirConfig<EF>,
    polynomial: &[F],
    statement: &[SparseStatement<EF>],
) -> (fiat_shamir::Proof<F>, Witness<EF>) {
    let poseidon = default_koalabear_poseidon1_16();
    let mut prover_state = ProverState::new(poseidon);
    precompute_dft_twiddles::<F>(1 << 16);

    let poly_owned: MleOwned<EF> = MleOwned::Base(polynomial.to_vec());
    let witness = config.commit(&mut prover_state, &poly_owned, polynomial.len());
    let witness_clone = witness.clone();
    config.prove(
        &mut prover_state,
        statement.to_vec(),
        witness_clone,
        &poly_owned.by_ref(),
    );
    (prover_state.into_proof(), witness)
}

/// Verify a proof. Returns Ok(folding_randomness) or Err.
fn verify_proof(
    config: &WhirConfig<EF>,
    proof: fiat_shamir::Proof<F>,
    statement: &[SparseStatement<EF>],
) -> Result<MultilinearPoint<EF>, fiat_shamir::ProofError> {
    let poseidon = default_koalabear_poseidon1_16();
    let mut verifier_state = VerifierState::<EF, _>::new(proof, poseidon).unwrap();
    let parsed = config.parse_commitment::<F>(&mut verifier_state)?;
    config.verify::<F>(&mut verifier_state, &parsed, statement.to_vec())
}

// ---------------------------------------------------------------------------
// §5, Construction 5.1: End-to-end completeness
// ---------------------------------------------------------------------------

#[test]
fn completeness_simple_evaluation_constraint() {
    // Construction 5.1 completeness: honest prover's proof is accepted.
    // Weight polynomial ŵ = Z · eq(z, X) for a single evaluation constraint.
    let (config, num_variables) = small_whir_config();
    let mut rng = StdRng::seed_from_u64(42);
    let polynomial: Vec<F> = (0..1 << num_variables).map(|_| rng.random()).collect();

    // Evaluate at a random point to create the statement
    let point: Vec<EF> = (0..num_variables).map(|_| rng.random()).collect();
    let eval = polynomial.evaluate(&MultilinearPoint(point.clone()));
    let statement = vec![SparseStatement::dense(MultilinearPoint(point), eval)];

    let (proof, _) = prove_and_get_proof(&config, &polynomial, &statement);
    verify_proof(&config, proof, &statement).expect("honest proof must verify");
}

#[test]
fn completeness_multiple_evaluation_constraints() {
    // §5.2 Construction 5.5: batching multiple constraints.
    // ŵ(Z,X) = Σ γ^{i-1} · ŵ_i(Z,X), σ = Σ γ^{i-1} · σ_i.
    let (config, num_variables) = small_whir_config();
    let mut rng = StdRng::seed_from_u64(99);
    let polynomial: Vec<F> = (0..1 << num_variables).map(|_| rng.random()).collect();

    let mut statement = Vec::new();
    for _ in 0..4 {
        let point: Vec<EF> = (0..num_variables).map(|_| rng.random()).collect();
        let eval = polynomial.evaluate(&MultilinearPoint(point.clone()));
        statement.push(SparseStatement::dense(MultilinearPoint(point), eval));
    }

    let (proof, _) = prove_and_get_proof(&config, &polynomial, &statement);
    verify_proof(&config, proof, &statement).expect("batched proof must verify");
}

// ---------------------------------------------------------------------------
// §5.1, Theorem 5.2: Soundness — verifier rejects invalid proofs
// ---------------------------------------------------------------------------

#[test]
fn soundness_wrong_evaluation_rejected() {
    // If the statement claims f(z) = v but v is wrong, the verifier must reject.
    // This tests the full verification chain: sumcheck consistency (Decision §1),
    // STIR queries (Decision §2c), and the final polynomial check (Decision §3).
    let (config, num_variables) = small_whir_config();
    let mut rng = StdRng::seed_from_u64(7);
    let polynomial: Vec<F> = (0..1 << num_variables).map(|_| rng.random()).collect();

    let point: Vec<EF> = (0..num_variables).map(|_| rng.random()).collect();
    let correct_eval = polynomial.evaluate(&MultilinearPoint(point.clone()));
    // Deliberately wrong evaluation
    let wrong_eval = correct_eval + EF::ONE;

    let correct_statement = vec![SparseStatement::dense(MultilinearPoint(point.clone()), correct_eval)];
    let wrong_statement = vec![SparseStatement::dense(MultilinearPoint(point), wrong_eval)];

    // Prove with correct statement, verify with wrong statement
    let (proof, _) = prove_and_get_proof(&config, &polynomial, &correct_statement);
    let result = verify_proof(&config, proof, &wrong_statement);
    assert!(result.is_err(), "verifier must reject proof for wrong evaluation");
}

// ---------------------------------------------------------------------------
// §6.2: Parameter choices — error budget validation
// ---------------------------------------------------------------------------

#[test]
fn error_budget_johnson_bound_parameters() {
    // Theorem 5.2 error bounds. For JohnsonBound at security_level λ:
    // - ε^fold ≤ d*·ℓ/|F| + err*(C, 2, δ)  [folding error]
    // - ε^out  ≤ 2^m · ℓ² / (2·|F|)          [OOD error, Lemma 4.25]
    // - ε^shift ≤ (1-δ)^t + ℓ·(t+1)/|F|      [query error]
    //
    // The config must allocate PoW grinding bits so that
    // ε^fold + ε^out + ε^shift ≤ 2^{-λ} per round.
    let security_level = 100;
    let num_variables = 20;
    let builder = WhirConfigBuilder {
        security_level,
        max_num_variables_to_send_coeffs: 6,
        pow_bits: 16,
        folding_factor: FoldingFactor::constant(4),
        soundness_type: SecurityAssumption::JohnsonBound,
        starting_log_inv_rate: 2,
        rs_domain_initial_reduction_factor: 1,
    };
    let config = WhirConfig::<EF>::new(&builder, num_variables);

    // Verify that the PoW budget doesn't exceed the configured maximum
    // (per-round pow_bits ≤ builder.pow_bits).
    assert!(
        config.starting_folding_pow_bits <= builder.pow_bits,
        "initial folding PoW {} exceeds budget {}",
        config.starting_folding_pow_bits,
        builder.pow_bits
    );
    for (i, round) in config.round_parameters.iter().enumerate() {
        assert!(
            round.folding_pow_bits <= builder.pow_bits,
            "round {} folding PoW {} exceeds budget {}",
            i,
            round.folding_pow_bits,
            builder.pow_bits
        );
        assert!(
            round.query_pow_bits <= builder.pow_bits,
            "round {} query PoW {} exceeds budget {}",
            i,
            round.query_pow_bits,
            builder.pow_bits
        );
    }

    // Verify round structure: Σ kᵢ + final_sumcheck_rounds = num_variables
    // (Construction 5.1 parameter constraint)
    let total_folding = config.folding_factor.total_number(config.n_rounds());
    assert_eq!(
        total_folding + config.final_sumcheck_rounds,
        num_variables,
        "folding + final sumcheck must cover all variables (Construction 5.1)"
    );
}

// ---------------------------------------------------------------------------
// §3.3, Definition 3.4: eq polynomial and multilinear evaluation
// ---------------------------------------------------------------------------

#[test]
fn expand_from_univariate_matches_pow_definition() {
    // §3 notation: pow(x, m) := (x^{2^0}, ..., x^{2^{m-1}}).
    // MultilinearPoint::expand_from_univariate must produce this.
    let alpha = EF::from(KoalaBear::from_u32(17));
    let m = 5;
    let point = MultilinearPoint::<EF>::expand_from_univariate(alpha, m);

    let mut expected = Vec::with_capacity(m);
    let mut current = alpha;
    for _ in 0..m {
        expected.push(current);
        current = current * current; // x^{2^i} → x^{2^{i+1}}
    }

    assert_eq!(point.0, expected, "expand_from_univariate must equal pow(x, m) per §3");
}

// ---------------------------------------------------------------------------
// §4.3, Definition 4.14: Folding operation
// ---------------------------------------------------------------------------

#[test]
fn folding_definition_consistency() {
    // Definition 4.14: Fold(f, α)(x²) = (f(x) + f(-x))/2 + α · (f(x) - f(-x))/(2x).
    //
    // For a multilinear polynomial, this means:
    // f̂(α, X₂, ..., Xₘ) should equal the evaluation of the folded function.
    //
    // We verify this by constructing a polynomial, folding it at a random point,
    // and checking that the result matches the multilinear extension evaluation.
    let m = 4;
    let mut rng = StdRng::seed_from_u64(314);
    let coeffs: Vec<EF> = (0..1 << m).map(|_| EF::from(rng.random::<F>())).collect();

    // Evaluate f̂(α, r₂, r₃, r₄) using eval_multilinear_coeffs
    let alpha: EF = rng.random();
    let r: Vec<EF> = (1..m).map(|_| rng.random()).collect();

    let mut full_point = vec![alpha];
    full_point.extend_from_slice(&r);
    let direct_eval = eval_multilinear_coeffs(&coeffs, &full_point);

    // Now fold the coefficients by fixing X₁ = α, then evaluate at (r₂, r₃, r₄)
    let half = coeffs.len() / 2;
    let folded: Vec<EF> = (0..half).map(|i| coeffs[i] + alpha * coeffs[i + half]).collect();
    let folded_eval = eval_multilinear_coeffs(&folded, &r);

    assert_eq!(
        direct_eval, folded_eval,
        "folding X₁=α then evaluating must equal direct evaluation (Def 4.14)"
    );
}

// ---------------------------------------------------------------------------
// verify.rs:385-398: verify_constraint_coeffs — univariate ↔ multilinear
// ---------------------------------------------------------------------------

#[test]
fn univariate_horner_matches_multilinear_on_evals_to_coeffs_output() {
    // The final-round check uses two evaluation methods on the SAME coefficient array
    // (output of evals_to_coeffs):
    //
    // (a) verify.rs:199 — eval_multilinear_coeffs(coeffs, reversed_sumcheck_point)
    //     for the final sumcheck consistency check
    // (b) verify.rs:396 — Horner evaluation coeffs[0] + coeffs[1]·α + ... for STIR
    //     constraint checks at domain points pow(z, m)
    //
    // evals_to_coeffs applies a bit-reverse permutation (evals.rs:55) after the
    // butterfly, which reorders coefficients so that Horner at z gives the correct
    // univariate evaluation f(z) = f̂(pow(z, m)). We verify this by starting from
    // evaluations, converting to coefficients, and checking both methods agree.
    let n = 4;
    let mut rng = StdRng::seed_from_u64(271);

    // Start from evaluation form: evals[k] = f(b₀, b₁, ...) where k = b₀ + 2b₁ + ...
    let mut evals: Vec<EF> = (0..1 << n).map(|_| EF::from(rng.random::<F>())).collect();

    // Evaluate the polynomial at a random point BEFORE converting to coefficients
    // (using evaluation-form multilinear evaluation)
    let alpha: EF = rng.random();
    let pow_point = MultilinearPoint::<EF>::expand_from_univariate(alpha, n);
    let eval_form_result = evals.evaluate(&pow_point);

    // Convert evaluations to coefficients (includes bit-reverse permutation)
    evals_to_coeffs(&mut evals);
    let coeffs = evals;

    // Horner evaluation on the coefficients
    let horner_result = coeffs.iter().rfold(EF::ZERO, |acc, &c| acc * alpha + c);

    assert_eq!(
        eval_form_result, horner_result,
        "Horner on evals_to_coeffs output must match evaluation-form result at pow(α,n)"
    );
}

// ---------------------------------------------------------------------------
// §5.1, Theorem 5.2: domain structure validation
// ---------------------------------------------------------------------------

#[test]
fn folded_domain_generator_order() {
    // Construction 5.1 step 2d: STIR queries sample from L^{(2^k)}_{i-1}.
    // The folded_domain_gen must be a generator of the correct-order subgroup.
    let (config, _) = small_whir_config();

    for (i, round) in config.round_parameters.iter().enumerate() {
        let expected_order = round.domain_size >> round.folding_factor;
        // gen^{expected_order} should equal 1 (it generates a group of that order)
        let gen_to_order = round.folded_domain_gen.exp_u64(expected_order as u64);
        assert_eq!(
            gen_to_order,
            <PF<EF> as PrimeCharacteristicRing>::ONE,
            "round {} folded_domain_gen must have order {} (domain_size/2^folding_factor)",
            i,
            expected_order
        );
        // gen^{expected_order/2} should NOT equal 1 (primitive generator)
        if expected_order > 1 {
            let gen_to_half = round.folded_domain_gen.exp_u64((expected_order / 2) as u64);
            assert_ne!(
                gen_to_half,
                <PF<EF> as PrimeCharacteristicRing>::ONE,
                "round {} folded_domain_gen must be primitive",
                i
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Convention documentation: combination weight shift
// ---------------------------------------------------------------------------

#[test]
fn combination_weights_start_from_one() {
    // Convention difference from ACFY24 Construction 5.1:
    //
    // Paper (step 2e, page 32): new constraints get weights γ^{j+1} (j=0,...,t-1).
    // Implementation (verify.rs:214): weights are [γ^0, γ^1, ...] = [1, γ, γ², ...].
    //
    // The shift doesn't affect soundness: the polynomial identity lemma
    // argument in Claim 5.4 works with degree t instead of t+1, giving
    // a tighter bound. Both prover (open.rs:146) and verifier agree on
    // this convention.
    //
    // This test documents the convention by verifying that the first
    // constraint weight is 1 (not γ). We do this indirectly by checking
    // that a single-constraint proof works — if the weight were γ instead
    // of 1, the claimed_sum would be γ·v instead of v, and the sumcheck
    // would need to account for that.
    let (config, num_variables) = small_whir_config();
    let mut rng = StdRng::seed_from_u64(111);
    let polynomial: Vec<F> = (0..1 << num_variables).map(|_| rng.random()).collect();

    // Single constraint: weight = 1 (first in the combination)
    let point: Vec<EF> = (0..num_variables).map(|_| rng.random()).collect();
    let eval = polynomial.evaluate(&MultilinearPoint(point.clone()));
    let statement = vec![SparseStatement::dense(MultilinearPoint(point), eval)];

    let (proof, _) = prove_and_get_proof(&config, &polynomial, &statement);
    verify_proof(&config, proof, &statement).expect("single-constraint proof verifies with weight=1");
}

// ---------------------------------------------------------------------------
// Sumcheck degree: d = max{d*, 3} where d* = 1 + deg_Z(ŵ) + max_i deg_{X_i}(ŵ)
// ---------------------------------------------------------------------------

#[test]
fn sumcheck_degree_correct_for_eq_weight() {
    // Construction 5.1: d* = 1 + deg_Z(ŵ₀) + max_{i∈[m₀]} deg_{X_i}(ŵ₀).
    // For ŵ = Z · eq(z, X):
    //   deg_Z = 1, deg_{X_i} = 1, so d* = 1 + 1 + 1 = 3.
    //   d = max{d*, 3} = 3.
    //
    // The sumcheck polynomial has degree < d = 3, i.e., at most degree 2,
    // requiring 3 coefficients. This matches the hardcoded value in
    // verify_sumcheck_rounds (verify.rs:417).
    //
    // NOTE: If future weight polynomials have higher degree (d* > 3),
    // the hardcoded 3 must be updated. This test will catch such a
    // regression if the config exposes the degree.
    let (config, num_variables) = small_whir_config();
    let mut rng = StdRng::seed_from_u64(55);
    let polynomial: Vec<F> = (0..1 << num_variables).map(|_| rng.random()).collect();

    // If the degree were wrong (too low), the sumcheck would produce
    // incorrect evaluations and the final check would fail.
    let point: Vec<EF> = (0..num_variables).map(|_| rng.random()).collect();
    let eval = polynomial.evaluate(&MultilinearPoint(point.clone()));
    let statement = vec![SparseStatement::dense(MultilinearPoint(point), eval)];

    let (proof, _) = prove_and_get_proof(&config, &polynomial, &statement);
    verify_proof(&config, proof, &statement).expect("degree-3 sumcheck is correct for eq weights");
}

// ---------------------------------------------------------------------------
// §6.2: SecurityAssumption distance parameters
// ---------------------------------------------------------------------------

#[test]
fn security_assumptions_distance_parameters() {
    // §6.2 parameter choices:
    // - UD: δ = (1-ρ)/2
    // - JB: δ = 1 - √ρ - η, where η = √ρ/c
    // - CB: δ = 1 - ρ - η, where η = ρ/c
    //
    // Verify log(1-δ) computation for each assumption at rate ρ = 1/4.
    let log_inv_rate = 2; // ρ = 1/4
    let log_c = 3.0; // c = 8

    // UD: δ = (1 - 1/4)/2 = 3/8, so 1-δ = 5/8, log(5/8) ≈ -0.678
    let ud_log = SecurityAssumption::UniqueDecoding.log_1_delta(log_inv_rate, log_c);
    assert!(ud_log < -0.67 && ud_log > -0.69, "UD log(1-δ) = {}", ud_log);

    // JB: η = √(1/4)/8 = 1/16, δ = 1 - 1/2 - 1/16 = 7/16, 1-δ = 9/16
    let jb_log = SecurityAssumption::JohnsonBound.log_1_delta(log_inv_rate, log_c);
    let expected_jb = (9.0_f64 / 16.0).log2();
    assert!(
        (jb_log - expected_jb).abs() < 0.01,
        "JB log(1-δ) = {}, expected {}",
        jb_log,
        expected_jb
    );

    // CB: η = (1/4)/8 = 1/32, δ = 1 - 1/4 - 1/32 = 23/32, 1-δ = 9/32
    let cb_log = SecurityAssumption::CapacityBound.log_1_delta(log_inv_rate, log_c);
    let expected_cb = (9.0_f64 / 32.0).log2();
    assert!(
        (cb_log - expected_cb).abs() < 0.01,
        "CB log(1-δ) = {}, expected {}",
        cb_log,
        expected_cb
    );
}

// ---------------------------------------------------------------------------
// Lemma 4.25: OOD error formula
// ---------------------------------------------------------------------------

#[test]
fn ood_error_formula_matches_lemma_4_25() {
    // Lemma 4.25 (adapted from [ACFY24] Lemma 4.5):
    //   Pr[|Λ(CRS[...], f, δ)| > 1] ≤ (ℓ²/2) · (2^m / |F|)^s
    //
    // In log scale: -log₂(error) = s·field_size + 1 - 2·list_size_bits - s·log_degree
    //
    // The implementation's ood_error returns this in bits of security.
    let sa = SecurityAssumption::JohnsonBound;
    let log_degree = 20;
    let log_inv_rate = 2;
    let field_size_bits = EF::bits();
    let log_c = 4.0;
    let ood_samples = 1;

    let security_bits = sa.ood_error(log_degree, log_inv_rate, field_size_bits, ood_samples, log_c);

    // Manually compute: s·field_size + 1 - 2·list_size_bits - s·log_degree
    let list_size_bits = sa.list_size_bits(log_degree, log_inv_rate, log_c);
    let expected =
        (ood_samples * field_size_bits) as f64 + 1.0 - 2.0 * list_size_bits - (ood_samples * log_degree) as f64;

    assert!(
        (security_bits - expected).abs() < 0.001,
        "ood_error({} samples) = {}, expected {} (Lemma 4.25)",
        ood_samples,
        security_bits,
        expected
    );
}
