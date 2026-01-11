use clap::Parser;
mod prove_poseidons;
use rec_aggregation::{recursion::run_recursion_benchmark, xmss_aggregate::run_xmss_benchmark};
use xmss::XMSS_MAX_LOG_LIFETIME;

use crate::prove_poseidons::benchmark_prove_poseidon_16;

#[derive(Parser)]
enum Cli {
    #[command(about = "Aggregate XMSS signature")]
    Xmss {
        #[arg(long)]
        n_signatures: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
    },
    #[command(about = "Run n->1 recursion")]
    Recursion {
        #[arg(long, default_value = "1", help = "Number of recursive proofs to aggregate")]
        n: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
    },
    #[command(about = "Prove validity of Poseidon2 permutations over 16 field elements")]
    Poseidon {
        #[arg(long, help = "log2(number of Poseidons)")]
        log_n_perms: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
    },
}

fn main() {
    let cli = Cli::parse();

    match cli {
        Cli::Xmss { n_signatures, tracing } => {
            let log_lifetimes = (0..n_signatures).map(|_| XMSS_MAX_LOG_LIFETIME).collect::<Vec<_>>();
            run_xmss_benchmark(&log_lifetimes, tracing);
        }
        Cli::Recursion { n, tracing } => {
            run_recursion_benchmark(n, tracing);
        }
        Cli::Poseidon {
            log_n_perms: log_count,
            tracing,
        } => {
            benchmark_prove_poseidon_16(log_count, tracing);
        }
    }
}
