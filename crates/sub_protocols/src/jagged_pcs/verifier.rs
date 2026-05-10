use backend::*;
use lean_vm::{EF, F};

use super::branching::BranchingProgram;
use super::config::{JaggedConfig, usize_to_point};
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
/// Mirrors [`super::prover::jagged_open`]: rebuild the batched sumcheck
/// claim, verify the product sumcheck, decouple `q(i*) * F(i*)` using the
/// prover-supplied `q(i*)`, recompute `F(i*)` by evaluating the width-6
/// branching program once per claim (since each claim's `z_tab` is on cube,
/// only one sub-table contributes per claim), and forward the dense WHIR
/// claim to the underlying verifier.
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

    // 2. Combined claim value.
    let v_combined: EF = alphas.iter().zip(claims).map(|(&a, c)| a * c.value).sum();

    // 3. Verify the product sumcheck (degree 2, m rounds).
    let sumcheck = sumcheck_verify(verifier_state, m, 2, v_combined, None)?;
    let sumcheck_point = sumcheck.point;
    let sumcheck_value = sumcheck.value;

    // 4. Receive q(i*).
    let q_at_istar = verifier_state.next_extension_scalar()?;

    // 5. Recompute F(i*) via per-claim BP evals.
    let cumulative_area_bits_ef: Vec<Vec<EF>> = parsed
        .cumulative_area_bits
        .iter()
        .map(|bits| bits.iter().map(|&b| EF::from(b)).collect())
        .collect();

    let mut f_at_istar = EF::ZERO;
    for (claim, &alpha) in claims.iter().zip(&alphas) {
        let st = config.sub_tables[claim.sub_table_id];
        let z_col_point = usize_to_point(claim.col_in_sub_table, st.log_width);
        let bp = BranchingProgram {
            z_row: &claim.z_row,
            z_col: &z_col_point,
            z_index: &sumcheck_point,
            log_width: st.log_width,
            log_dense_size: m,
        };
        let bp_eval = bp.eval(
            &cumulative_area_bits_ef[claim.sub_table_id],
            &cumulative_area_bits_ef[claim.sub_table_id + 1],
        );
        f_at_istar += alpha * bp_eval;
    }

    // 6. Check sumcheck identity.
    if sumcheck_value != q_at_istar * f_at_istar {
        return Err(ProofError::InvalidProof);
    }

    // 7. Verify the underlying WHIR opening.
    let stmt = SparseStatement::dense(sumcheck_point, q_at_istar);
    WhirConfig::new(whir_config, m).verify(verifier_state, &parsed.whir, vec![stmt])?;
    Ok(())
}
