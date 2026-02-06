use clap::Parser;
mod prove_poseidons;
use rec_aggregation::{recursion::run_recursion_benchmark, xmss_aggregate::run_xmss_benchmark};

use crate::prove_poseidons::benchmark_prove_poseidon_16;

#[derive(Parser)]
enum Cli {
    #[command(about = "Aggregate XMSS signature")]
    Xmss {
        #[arg(long)]
        n_signatures: usize,
        #[arg(long, help = "log(1/rate) in WHIR", default_value = "1", short = 'r')]
        log_inv_rate: usize,
        // TODO use the latest results (i.e. update the conjecture)
        #[arg(long, help = "Uses Conjecture 4.12 from WHIR (up to capacity)")]
        prox_gaps_conjecture: bool,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
    },
    #[command(about = "Run n->1 recursion")]
    Recursion {
        #[arg(long, default_value = "1", help = "Number of recursive proofs to aggregate")]
        n: usize,
        #[arg(long, help = "log(1/rate) in WHIR", default_value = "2", short = 'r')]
        log_inv_rate: usize,
        // TODO use the latest results (i.e. update the conjecture)
        #[arg(long, help = "Uses Conjecture 4.12 from WHIR (up to capacity)")]
        prox_gaps_conjecture: bool,
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
        Cli::Xmss {
            n_signatures,
            log_inv_rate,
            prox_gaps_conjecture,
            tracing,
        } => {
            run_xmss_benchmark(n_signatures, log_inv_rate, prox_gaps_conjecture, tracing);
        }
        Cli::Recursion {
            n,
            log_inv_rate,
            prox_gaps_conjecture,
            tracing,
        } => {
            run_recursion_benchmark(n, log_inv_rate, prox_gaps_conjecture, tracing);
        }
        Cli::Poseidon {
            log_n_perms: log_count,
            tracing,
        } => {
            benchmark_prove_poseidon_16(log_count, tracing);
        }
    }
}
