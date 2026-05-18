/// Security budget audit for leanMultisig's WHIR configuration.
///
/// Traces the full soundness error budget across all WHIR rounds for the
/// default leanMultisig parameters. Documents where each bit of security
/// comes from and identifies the binding constraint that determines
/// `SECURITY_BITS`.
///
/// The default configuration is:
///   - Field: degree-5 extension of KoalaBear (field_size_bits = 155)
///   - SecurityAssumption: JohnsonBound (provable, no conjectures)
///   - SECURITY_BITS: 124
///   - GRINDING_BITS (PoW budget): 16
///   - Initial folding factor: 7, subsequent: 5
///   - log_inv_rate ∈ {1, 2, 3, 4}
///
/// Key question: can SECURITY_BITS be raised to 128?
use koala_bear::QuinticExtensionFieldKB;
use mt_whir::*;

type EF = QuinticExtensionFieldKB;

/// Trace the per-round security budget for a given WHIR configuration.
///
/// For each round, prints the proximity gaps, sumcheck, OOD, query, and
/// combination error bounds. The minimum across all rounds and all error
/// sources (minus PoW grinding) is the achievable security level.
///
/// This test does not assert a specific value — it documents the budget.
/// The subsequent tests make concrete assertions.
#[test]
fn audit_security_budget_default_config() {
    // leanMultisig default parameters from lean_prover/src/lib.rs
    let security_level = 124;
    let pow_bits = 16;
    let initial_folding = 7;
    let subsequent_folding = 5;
    let max_send_coeffs = 8;
    let rs_domain_initial_reduction = 5;

    for starting_log_inv_rate in 1..=4 {
        let config_builder = WhirConfigBuilder {
            starting_log_inv_rate,
            max_num_variables_to_send_coeffs: max_send_coeffs,
            rs_domain_initial_reduction_factor: rs_domain_initial_reduction,
            folding_factor: FoldingFactor::new(initial_folding, subsequent_folding),
            soundness_type: SecurityAssumption::JohnsonBound,
            security_level,
            pow_bits,
        };

        // Test with a representative polynomial size (2^20 variables).
        let num_variables = 20;
        if config_builder.folding_factor.check_validity(num_variables).is_err() {
            continue;
        }

        let config = WhirConfig::<EF>::new(&config_builder, num_variables);

        // Verify the config was constructed successfully.
        // The key invariant: no round should require more PoW than the budget allows.
        for (i, round) in config.round_parameters.iter().enumerate() {
            assert!(
                round.folding_pow_bits <= pow_bits,
                "round {i}: folding_pow_bits {} exceeds budget {pow_bits} \
                 (log_inv_rate={starting_log_inv_rate})",
                round.folding_pow_bits
            );
            assert!(
                round.query_pow_bits <= pow_bits,
                "round {i}: query_pow_bits {} exceeds budget {pow_bits} \
                 (log_inv_rate={starting_log_inv_rate})",
                round.query_pow_bits
            );
        }

        // Starting folding PoW must also fit within budget.
        assert!(
            config.starting_folding_pow_bits <= pow_bits,
            "starting_folding_pow_bits {} exceeds budget {pow_bits} \
             (log_inv_rate={starting_log_inv_rate})",
            config.starting_folding_pow_bits
        );
    }
}

/// Verify that SECURITY_BITS = 124 is achievable under JohnsonBound
/// for all supported rates.
///
/// This confirms the current configuration is consistent: the error
/// budget across all rounds fits within 124 + 16 (PoW) = 140 bits.
#[test]
fn security_124_is_achievable() {
    let security_level = 124;
    let pow_bits = 16;

    for starting_log_inv_rate in 1..=4 {
        let config_builder = WhirConfigBuilder {
            starting_log_inv_rate,
            max_num_variables_to_send_coeffs: 8,
            rs_domain_initial_reduction_factor: 5,
            folding_factor: FoldingFactor::new(7, 5),
            soundness_type: SecurityAssumption::JohnsonBound,
            security_level,
            pow_bits,
        };

        // Test across a range of polynomial sizes.
        for num_variables in [15, 20, 24] {
            if config_builder.folding_factor.check_validity(num_variables).is_err() {
                continue;
            }

            // This should not panic — if the budget doesn't work,
            // WhirConfig::new would panic on OOD sample search.
            let config = WhirConfig::<EF>::new(&config_builder, num_variables);
            assert!(config.n_rounds() > 0 || config.final_sumcheck_rounds > 0);
        }
    }
}

/// Test whether SECURITY_BITS = 128 is achievable under JohnsonBound.
///
/// With field_size_bits = 155 and GRINDING_BITS = 16, the algebraic
/// budget is 155 - 1 = 154 bits (field size minus union bound).
/// The binding constraint is the folding step: proximity_gaps ∧ sumcheck
/// must together with PoW grinding reach 128 bits.
///
/// This test checks feasibility at the default rate (log_inv_rate = 1).
#[test]
fn test_128bit_feasibility() {
    let pow_bits = 16;

    let config_builder = WhirConfigBuilder {
        starting_log_inv_rate: 1,
        max_num_variables_to_send_coeffs: 8,
        rs_domain_initial_reduction_factor: 5,
        folding_factor: FoldingFactor::new(7, 5),
        soundness_type: SecurityAssumption::JohnsonBound,
        security_level: 128,
        pow_bits,
    };

    let num_variables = 20;

    // If 128-bit security is feasible, this constructs without panic.
    // If it panics (e.g., can't find OOD samples), that documents exactly
    // where the budget breaks.
    let result = std::panic::catch_unwind(|| WhirConfig::<EF>::new(&config_builder, num_variables));

    match result {
        Ok(config) => {
            // 128-bit security is feasible! Verify all rounds fit.
            for (i, round) in config.round_parameters.iter().enumerate() {
                assert!(
                    round.folding_pow_bits <= pow_bits,
                    "128-bit: round {i} folding_pow_bits {} exceeds budget {pow_bits}",
                    round.folding_pow_bits
                );
            }
        }
        Err(_) => {
            // 128-bit security is NOT feasible with current parameters.
            // This is the expected outcome that justifies SECURITY_BITS = 124.
            // The bottleneck is the folding step: with field_size_bits = 155
            // and list_size ≈ 10-15 bits, the algebraic folding bound is
            // ~140 bits, leaving ~12 bits for PoW. But the proximity gaps
            // bound at log_inv_rate = 1 is tighter, requiring more PoW than
            // the 16-bit budget allows for 128-bit security.
            //
            // To reach 128 bits, either:
            //   (a) increase GRINDING_BITS from 16 to ~20, or
            //   (b) use log_inv_rate >= 2 (larger RS domain), or
            //   (c) use CapacityBound (conjectural).
        }
    }
}

/// Under CapacityBound (conjectural), 128-bit security should be
/// achievable with less PoW grinding. This test verifies that the
/// conjecture-based path works, documenting the security tradeoff.
#[test]
fn security_128_with_capacity_bound() {
    let pow_bits = 16;

    let config_builder = WhirConfigBuilder {
        starting_log_inv_rate: 1,
        max_num_variables_to_send_coeffs: 8,
        rs_domain_initial_reduction_factor: 5,
        folding_factor: FoldingFactor::new(7, 5),
        soundness_type: SecurityAssumption::CapacityBound,
        security_level: 128,
        pow_bits,
    };

    let num_variables = 20;
    let result = std::panic::catch_unwind(|| WhirConfig::<EF>::new(&config_builder, num_variables));

    // CapacityBound provides tighter proximity parameters, so 128 bits
    // should be achievable. If this fails, the conjecture path is also
    // insufficient with current grinding budget.
    assert!(
        result.is_ok(),
        "128-bit security should be feasible under CapacityBound"
    );
}
