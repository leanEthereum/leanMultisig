use clap::Parser;
use lean_vm::benchmark_prove_poseidon_16;
use rec_aggregation::{whir_recursion::run_whir_recursion_benchmark, xmss_aggregate::run_xmss_benchmark};
use xmss::XMSS_MAX_LOG_LIFETIME;

#[derive(Parser)]
enum Cli {
    #[command(about = "Aggregate XMSS signature")]
    Xmss {
        #[arg(long)]
        n_signatures: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
    },
    #[command(about = "Run 1 WHIR recursive proof")]
    Recursion {
        #[arg(long, default_value_t = 1, help = "Number of recursions")]
        count: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
        #[arg(long, help = "Enable VM profiler")]
        profiler: bool,
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
        Cli::Recursion {
            count,
            tracing,
            profiler,
        } => {
            run_whir_recursion_benchmark(count, tracing, profiler);
        }
        Cli::Poseidon {
            log_n_perms: log_count,
            tracing,
        } => {
            benchmark_prove_poseidon_16(1 << log_count, tracing);
        }
    }
}
