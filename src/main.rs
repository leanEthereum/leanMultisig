use clap::Parser;
mod prove_poseidons;

use crate::prove_poseidons::benchmark_prove_poseidon_16;

#[derive(Parser)]
enum Cli {
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
        Cli::Poseidon {
            log_n_perms: log_count,
            tracing,
        } => {
            benchmark_prove_poseidon_16(log_count, tracing);
        }
    }
}
