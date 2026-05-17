//! Dump the float-derived parts of every reachable `WhirConfig` to
//! `crates/lean_prover/whir_configs.json` so the Python verifier doesn't have
//! to redo the soundness-formula computation in pure Python.
//!
//! Only the values that come from f64 math are dumped (query counts, OOD
//! samples, grinding bits). Everything else (per-round `num_variables`,
//! `domain_size`, `folding_factor`, `log_inv_rate`, `folded_domain_gen`,
//! `n_rounds`, `final_sumcheck_rounds`, `final_log_inv_rate`) is integer
//! arithmetic and is derived on the Python side.
//!
//! Run:
//!     cargo test -p lean_prover --test dump_whir_configs -- --nocapture

use std::fs;
use std::path::PathBuf;

use backend::{TwoAdicField, WhirConfig};
use lean_prover::default_whir_config;
use lean_vm::{EF, F, MAX_WHIR_LOG_INV_RATE, MIN_WHIR_LOG_INV_RATE};
use serde::Serialize;

#[derive(Serialize)]
struct Round {
    num_queries: usize,
    ood_samples: usize,
    query_pow_bits: usize,
    folding_pow_bits: usize,
}

#[derive(Serialize)]
struct Config {
    log_inv_rate: usize,
    num_variables: usize,
    commitment_ood_samples: usize,
    starting_folding_pow_bits: usize,
    final_queries: usize,
    final_query_pow_bits: usize,
    rounds: Vec<Round>,
}

#[test]
fn dump_whir_configs() {
    let mut configs = Vec::new();

    for log_inv_rate in MIN_WHIR_LOG_INV_RATE..=MAX_WHIR_LOG_INV_RATE {
        let builder = default_whir_config(log_inv_rate);
        let first_ff = builder.folding_factor.at_round(0);

        let min_nv = first_ff;
        let max_nv = F::TWO_ADICITY + first_ff - log_inv_rate;

        for num_variables in min_nv..=max_nv {
            let cfg: WhirConfig<EF> = WhirConfig::new(&builder, num_variables);

            let rounds = cfg
                .round_parameters
                .iter()
                .map(|r| Round {
                    num_queries: r.num_queries,
                    ood_samples: r.ood_samples,
                    query_pow_bits: r.query_pow_bits,
                    folding_pow_bits: r.folding_pow_bits,
                })
                .collect();

            configs.push(Config {
                log_inv_rate,
                num_variables,
                commitment_ood_samples: cfg.commitment_ood_samples,
                starting_folding_pow_bits: cfg.starting_folding_pow_bits,
                final_queries: cfg.final_queries,
                final_query_pow_bits: cfg.final_query_pow_bits,
                rounds,
            });
        }
    }

    let json = serde_json::to_string_pretty(&configs).unwrap();
    let path = std::env::var("WHIR_DUMP_PATH").map(PathBuf::from).unwrap_or_else(|_| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("whir_configs.json")
    });
    fs::write(&path, json).unwrap_or_else(|e| panic!("failed to write {}: {e}", path.display()));
    println!("wrote {} WhirConfig entries to {}", configs.len(), path.display());
}
