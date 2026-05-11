/// Tests for Fiat-Shamir challenger hardening:
///   - Rejection sampling uniformity (chi-squared)
///   - Prover-verifier transcript synchronization
///   - Deterministic output stability
use field::PrimeCharacteristicRing;
use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon1_16};
use mt_fiat_shamir::{ChallengeSampler, FSProver, FSVerifier, ProverState, VerifierState};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

/// Helper: create a fresh ProverState for testing.
fn fresh_prover() -> ProverState<EF, impl symetric::Compression<[F; 16]>> {
    ProverState::<EF, _>::new(default_koalabear_poseidon1_16())
}

// -----------------------------------------------------------------------
// Rejection sampling uniformity
// -----------------------------------------------------------------------

/// Verify that `sample_in_range` produces a uniform distribution over `[0, 2^bits)`.
///
/// We draw `n_samples` values, bin them into `2^bits` buckets, and run a chi-squared
/// goodness-of-fit test against the uniform distribution. The null hypothesis is that
/// all buckets are equally likely; we reject at p < 0.001 to avoid flaky tests.
///
/// For bits = 4 (16 buckets) with 16000 samples, expected count per bucket = 1000.
/// Chi-squared critical value for df=15, p=0.001 is ~37.7.
#[test]
fn test_sample_in_range_uniformity() {
    let mut prover = fresh_prover();

    let bits = 4;
    let n_buckets = 1usize << bits;
    let samples_per_bucket = 1000;
    let n_samples = n_buckets * samples_per_bucket;
    let expected = samples_per_bucket as f64;

    let samples = prover.sample_in_range(bits, n_samples);
    assert_eq!(samples.len(), n_samples);

    // All values must be in range.
    for &s in &samples {
        assert!(s < n_buckets, "sample {s} out of range [0, {n_buckets})");
    }

    // Compute chi-squared statistic.
    let mut counts = vec![0usize; n_buckets];
    for &s in &samples {
        counts[s] += 1;
    }

    let chi_sq: f64 = counts
        .iter()
        .map(|&c| {
            let diff = c as f64 - expected;
            diff * diff / expected
        })
        .sum();

    // Critical value for df=15, p=0.001 is ~37.7. Use 50.0 for extra margin.
    assert!(
        chi_sq < 50.0,
        "chi-squared {chi_sq:.1} exceeds threshold 50.0 — distribution is not uniform \
         (counts: {counts:?})"
    );
}

/// Verify uniformity at a higher bit width (bits = 8, 256 buckets).
/// This exercises the rejection threshold closer to realistic WHIR query sampling.
#[test]
fn test_sample_in_range_uniformity_8bit() {
    let mut prover = fresh_prover();

    let bits = 8;
    let n_buckets = 1usize << bits;
    let samples_per_bucket = 200;
    let n_samples = n_buckets * samples_per_bucket;
    let expected = samples_per_bucket as f64;

    let samples = prover.sample_in_range(bits, n_samples);

    let mut counts = vec![0usize; n_buckets];
    for &s in &samples {
        assert!(s < n_buckets);
        counts[s] += 1;
    }

    let chi_sq: f64 = counts
        .iter()
        .map(|&c| {
            let diff = c as f64 - expected;
            diff * diff / expected
        })
        .sum();

    // df=255, p=0.001 critical value ≈ 330. Use 350 for margin.
    assert!(
        chi_sq < 350.0,
        "chi-squared {chi_sq:.1} exceeds threshold 350.0 — distribution is not uniform"
    );
}

// -----------------------------------------------------------------------
// Prover-verifier transcript synchronization
// -----------------------------------------------------------------------

/// After the rejection sampling change, the prover and verifier must still
/// produce identical challenger states. This test runs a minimal prove-verify
/// cycle through the public API to confirm transcript synchronization.
///
/// The test is end-to-end: if rejection sampling desynchronized the Fiat-Shamir
/// transcript, the verifier would reject the proof.
#[test]
fn test_prover_verifier_transcript_sync() {
    let compressor = default_koalabear_poseidon1_16();
    let mut prover = ProverState::<EF, _>::new(compressor.clone());

    // Step 1: observe some scalars
    let data: Vec<F> = (0..8).map(|i| F::from_usize(i * 7 + 3)).collect();
    prover.add_base_scalars(&data);

    // Step 2: sample challenges (exercises sample_in_range)
    let challenges: Vec<usize> = prover.sample_in_range(10, 5);
    assert_eq!(challenges.len(), 5);
    for &c in &challenges {
        assert!(c < 1024);
    }

    // Step 3: sample extension field elements
    let ext_challenges: Vec<EF> = prover.sample_vec(3);
    assert_eq!(ext_challenges.len(), 3);

    // Step 4: PoW grinding
    prover.pow_grinding(8);

    // Serialize the proof
    let proof = prover.into_proof();

    // Step 5: Verify — if transcript desynchronized, this fails
    let mut verifier = VerifierState::<EF, _>::new(proof, compressor).unwrap();

    // Replay: verifier reads the same data
    let read_data = verifier.next_base_scalars_vec(8).unwrap();
    assert_eq!(read_data, data);

    // Replay: verifier samples the same challenges
    let v_challenges: Vec<usize> = verifier.sample_in_range(10, 5);
    assert_eq!(
        v_challenges, challenges,
        "sample_in_range must produce identical values for prover and verifier"
    );

    // Replay: verifier samples the same extension elements
    let v_ext: Vec<EF> = verifier.sample_vec(3);
    assert_eq!(v_ext, ext_challenges);

    // Replay: verifier checks PoW
    verifier.check_pow_grinding(8).expect("PoW grinding check must pass");
}

// -----------------------------------------------------------------------
// Deterministic output stability
// -----------------------------------------------------------------------

/// Two ProverStates initialized from the same compressor must produce
/// identical `sample_in_range` output at each bit width. This confirms
/// the function is deterministic (no hidden randomness source).
#[test]
fn test_sample_in_range_deterministic() {
    let compressor = default_koalabear_poseidon1_16();
    let mut p1 = ProverState::<EF, _>::new(compressor.clone());
    let mut p2 = ProverState::<EF, _>::new(compressor);

    for bits in [1, 4, 8, 16, 24] {
        let s1 = p1.sample_in_range(bits, 100);
        let s2 = p2.sample_in_range(bits, 100);
        assert_eq!(s1, s2, "sample_in_range must be deterministic for bits={bits}");
    }
}
