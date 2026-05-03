//! Dump the WhirConfig for given (num_variables, log_inv_rate) as
//! per-codeword JSON, ready for soundcalc to consume.
//!
//! Each entry in `codewords[i]` carries everything soundcalc needs for that
//! iteration: the (num_vars, log_inv_rate) of the code, the JBR multiplicity
//! `m`, the fold factor `k_i`, the folding/query PoW, the query count, and
//! the OOD samples received in this iteration.
//!
//! Used by `scripts/check_whir_soundness.py`.

use backend::WhirConfig;
use clap::Parser;
use lean_prover::default_whir_config;
use lean_vm::EF;
use serde_json::json;

#[derive(Parser)]
struct Cli {
    #[arg(long)]
    num_variables: usize,
    #[arg(long)]
    log_inv_rate: usize,
}

fn main() {
    let cli = Cli::parse();
    let builder = default_whir_config(cli.log_inv_rate);
    let cfg = WhirConfig::<EF>::new(&builder, cli.num_variables);
    let n_rounds = cfg.round_parameters.len();

    let codewords: Vec<_> = (0..=n_rounds)
        .map(|i| {
            let prev = (i > 0).then(|| &cfg.round_parameters[i - 1]);
            let next = (i < n_rounds).then(|| &cfg.round_parameters[i]);
            json!({
                "num_vars":       prev.map_or(cfg.num_variables,        |p| p.num_variables),
                "log_inv_rate":   next.map_or(cfg.final_log_inv_rate,   |n| n.log_inv_rate),
                "m":              cfg.jbr_multiplicities[i],
                "fold_factor":    cfg.folding_factor.at_round(usize::from(i != 0)),
                // Folding PoW grinding was removed on the goldilocks branch (commit 37f052fd):
                // not needed when the field is big enough (cubic extension of Goldilocks ≈ 192 bits).
                "fold_pow":       0,
                "queries":        next.map_or(cfg.final_queries,        |n| n.num_queries),
                "query_pow":      next.map_or(cfg.final_query_pow_bits, |n| n.query_pow_bits),
                "ood_samples":    prev.map_or(0,                        |p| p.ood_samples),
            })
        })
        .collect();

    println!(
        "{}",
        json!({
            "codewords": codewords,
            "constraint_degree": 3,  // max(d*, 3) per WHIR Construction 5.1
        })
    );
}
