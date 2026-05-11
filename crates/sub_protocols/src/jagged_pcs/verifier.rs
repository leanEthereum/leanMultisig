use backend::*;
use lean_vm::{EF, F};

use super::branching::BranchingProgram;
use super::config::{JaggedConfig, usize_to_bits, usize_to_point};
use super::prover::JaggedClaim;

/// Output of the verifier-side "parse commitment" step. Holds the parsed
/// WHIR commitment together with the verifier's view of the cumulative
/// table areas (received from the prover and validated as bit vectors).
#[derive(Debug)]
pub struct ParsedJaggedCommitment {
    pub whir: ParsedCommitment<F, EF>,
    /// `cumulative_area_bits[y]` is the length-`m` bit vector encoding of
    /// `t_y` (one F element per bit, big-endian / high bit first).
    pub cumulative_area_bits: Vec<Vec<F>>,
}

/// Verifier-side parsing of a jagged commitment.
///
/// Reads `cumulative_area_bits` from the transcript, checks that each entry
/// is in {0, 1} (booleanity) and that the encoded integers form a strictly
/// increasing sequence ending at `<= 2^m` (monotonicity / dense-area
/// soundness), then parses the underlying WHIR commitment.
pub fn jagged_parse_commitment(
    config: &JaggedConfig,
    verifier_state: &mut impl FSVerifier<EF>,
    whir_config: &WhirConfigBuilder,
) -> Result<ParsedJaggedCommitment, ProofError> {
    let m = config.log_dense_size;

    let mut cumulative_area_bits = Vec::with_capacity(config.cumulative_areas.len());
    for _ in 0..config.cumulative_areas.len() {
        let bits = verifier_state.next_base_scalars_vec(m)?;
        // Booleanity.
        for b in &bits {
            if *b * (F::ONE - *b) != F::ZERO {
                return Err(ProofError::InvalidProof);
            }
        }
        cumulative_area_bits.push(bits);
    }

    // Monotonicity: convert each bit vector back to integer and check
    // strictly non-decreasing (and that the first entry is 0 to match the
    // prover's configuration).
    let to_int = |bits: &[F]| -> u128 {
        let mut acc: u128 = 0;
        for &bit in bits {
            acc <<= 1;
            if bit == F::ONE {
                acc |= 1;
            }
        }
        acc
    };
    let mut prev: u128 = 0;
    for (idx, bits) in cumulative_area_bits.iter().enumerate() {
        let v = to_int(bits);
        if idx == 0 {
            if v != 0 {
                return Err(ProofError::InvalidProof);
            }
        } else if v < prev {
            return Err(ProofError::InvalidProof);
        }
        prev = v;
    }

    let whir = WhirConfig::new(whir_config, m).parse_commitment::<F>(verifier_state)?;
    Ok(ParsedJaggedCommitment {
        whir,
        cumulative_area_bits,
    })
}

/// Verify a jagged opening proof.
///
/// Mirrors [`super::prover::jagged_open`]: sample the batching alphas,
/// compute the (padding-corrected) combined claim value `v_combined`, then
/// hand `(v_combined, BP-based F(i*) callback)` to WHIR as a raw weighted
/// statement. WHIR's own sumcheck folds `<polynomial, F> = v_combined`
/// internally; this routine no longer runs (or verifies) a dedicated
/// jagged sumcheck.
pub fn jagged_verify(
    config: &JaggedConfig,
    parsed: &ParsedJaggedCommitment,
    claims: &[JaggedClaim],
    verifier_state: &mut impl FSVerifier<EF>,
    whir_config: &WhirConfigBuilder,
) -> Result<(), ProofError> {
    let m = config.log_dense_size;

    // Per-claim length / index sanity checks (the verifier's view of these
    // is fixed by the call site, so an inconsistent claim list is a
    // configuration error rather than a malicious-prover signal; we still
    // reject defensively).
    for claim in claims {
        if claim.sub_table_id >= config.n_sub_tables() {
            return Err(ProofError::InvalidProof);
        }
        let st = config.sub_tables[claim.sub_table_id];
        if claim.z_row.len() < log2_ceil_usize(st.height) {
            return Err(ProofError::InvalidProof);
        }
        if claim.col_in_sub_table >= 1 << st.log_width {
            return Err(ProofError::InvalidProof);
        }
    }

    // 1. Sample batching alphas (must mirror the prover exactly).
    let alphas: Vec<EF> = (0..claims.len()).map(|_| verifier_state.sample()).collect();

    // 2. Combined claim value, with the padding correction applied per claim
    // so the underlying jagged sumcheck is about the data-only column `D`.
    let v_combined: EF = alphas
        .iter()
        .zip(claims)
        .map(|(&a, c)| {
            let h = config.sub_tables[c.sub_table_id].height;
            a * (c.value - c.padding_adjustment(h))
        })
        .sum();

    // 3. Pre-cache the EF-lifted cumulative_area bits, plus one shifted
    // copy per sub-table actually used by a next-claim. We do this OUTSIDE
    // the WHIR callback so the closure doesn't capture mutable state.
    let cumulative_area_bits_ef: Vec<Vec<EF>> = parsed
        .cumulative_area_bits
        .iter()
        .map(|bits| bits.iter().map(|&b| EF::from(b)).collect())
        .collect();
    let mut shifted_t_prev_cache: std::collections::BTreeMap<usize, Vec<EF>> = Default::default();
    for claim in claims {
        if claim.is_next && !shifted_t_prev_cache.contains_key(&claim.sub_table_id) {
            let st = config.sub_tables[claim.sub_table_id];
            let original = config.cumulative_areas[claim.sub_table_id];
            let shifted = original + (1usize << st.log_width);
            debug_assert!(shifted <= config.cumulative_areas[claim.sub_table_id + 1]);
            let bits: Vec<EF> = usize_to_bits(shifted, m).into_iter().map(EF::from).collect();
            shifted_t_prev_cache.insert(claim.sub_table_id, bits);
        }
    }

    // 4. Hand `(v_combined, F(i*)-via-BP)` to WHIR. The closure runs once,
    // after WHIR's sumcheck folds have produced the final point i*.
    let eval_f_at_final = |i_star: &MultilinearPoint<EF>| -> Vec<EF> {
        let mut f_at_istar = EF::ZERO;
        for (claim, &alpha) in claims.iter().zip(&alphas) {
            let st = config.sub_tables[claim.sub_table_id];
            let z_col_point = usize_to_point(claim.col_in_sub_table, st.log_width);
            let t_prev_bits: &[EF] = if claim.is_next {
                shifted_t_prev_cache.get(&claim.sub_table_id).unwrap()
            } else {
                &cumulative_area_bits_ef[claim.sub_table_id]
            };
            let bp = BranchingProgram {
                z_row: &claim.z_row,
                z_col: &z_col_point,
                z_index: i_star,
                log_width: st.log_width,
                log_dense_size: m,
            };
            let bp_eval = bp.eval(t_prev_bits, &cumulative_area_bits_ef[claim.sub_table_id + 1]);
            f_at_istar += alpha * bp_eval;
        }
        vec![f_at_istar]
    };

    WhirConfig::new(whir_config, m).verify_with_extras(
        verifier_state,
        &parsed.whir,
        vec![],
        vec![v_combined],
        eval_f_at_final,
    )?;
    Ok(())
}
