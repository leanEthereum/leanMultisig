use clap::Parser;
use poseidon_circuit::tests::run_poseidon_benchmark;
use rec_aggregation::{recursion::run_whir_recursion_benchmark, xmss_aggregate::run_xmss_benchmark};

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
        Cli::Xmss { n_signatures: count } => {
            run_xmss_benchmark(count);
        }
        Cli::Recursion => {
            run_whir_recursion_benchmark();
        }
        Cli::Poseidon { log_n_perms: log_count } => {
            run_poseidon_benchmark::<16, 16, 3>(log_count, false);
        }
    }
}
