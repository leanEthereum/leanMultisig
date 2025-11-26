use clap::Parser;
use poseidon_circuit::tests::run_poseidon_benchmark;
use rec_aggregation::{recursion::run_whir_recursion_benchmark, xmss_aggregate::run_xmss_benchmark};
use xmss::XMSS_MAX_LOG_LIFETIME;

#[derive(Parser)]
enum Cli {
    #[command(about = "Aggregate XMSS signature")]
    Xmss {
        #[arg(long)]
        n_signatures: usize,
    },
    #[command(about = "Run 1 WHIR recursive proof")]
    Recursion,
    #[command(about = "Prove validity of Poseidon2 permutations over 16 field elements")]
    Poseidon {
        #[arg(long, help = "log2(number of Poseidons)")]
        log_n_perms: usize,
    },
}

fn main() {
    let cli = Cli::parse();

    match cli {
        Cli::Xmss { n_signatures } => {
            let log_lifetimes = (0..n_signatures).map(|_| XMSS_MAX_LOG_LIFETIME).collect::<Vec<_>>();
            run_xmss_benchmark(&log_lifetimes);
        }
        Cli::Recursion => {
            run_whir_recursion_benchmark();
        }
        Cli::Poseidon { log_n_perms: log_count } => {
            run_poseidon_benchmark::<16, 16, 3>(log_count, false);
        }
    }
}
