use clap::Parser;
use rec_aggregation::{AggregationTopology, benchmark::run_aggregation_benchmark};
mod prove_poseidons;

use crate::prove_poseidons::benchmark_prove_poseidon_16;

#[derive(Parser)]
enum Cli {
    #[command(about = "Aggregate XMSS")]
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
    #[command(about = "Run a fancy aggregation topology")]
    FancyAggregation {
        // TODO use the latest results (i.e. update the conjecture)
        #[arg(long, help = "Uses Conjecture 4.12 from WHIR (up to capacity)")]
        prox_gaps_conjecture: bool,
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
            let topology = AggregationTopology {
                raw_xmss: n_signatures,
                children: vec![],
                log_inv_rate,
            };
            run_aggregation_benchmark(&topology, 0, prox_gaps_conjecture, tracing);
        }
        Cli::Recursion {
            n,
            log_inv_rate,
            prox_gaps_conjecture,
            tracing,
        } => {
            let topology = AggregationTopology {
                raw_xmss: 0,
                children: vec![
                    AggregationTopology {
                        raw_xmss: 10,
                        children: vec![],
                        log_inv_rate,
                    };
                    n
                ],
                log_inv_rate,
            };
            run_aggregation_benchmark(&topology, 0, prox_gaps_conjecture, tracing);
        }
        Cli::Poseidon {
            log_n_perms: log_count,
            tracing,
        } => {
            benchmark_prove_poseidon_16(log_count, tracing);
        }
        Cli::FancyAggregation { prox_gaps_conjecture } => {
            let topology = AggregationTopology {
                raw_xmss: 10,
                children: vec![AggregationTopology {
                    raw_xmss: 0,
                    children: vec![
                        AggregationTopology {
                            raw_xmss: 10,
                            children: vec![AggregationTopology {
                                raw_xmss: 25,
                                children: vec![
                                    AggregationTopology {
                                        raw_xmss: 1400,
                                        children: vec![],
                                        log_inv_rate: 1,
                                    };
                                    3
                                ],
                                log_inv_rate: 1,
                            }],
                            log_inv_rate: 3,
                        },
                        AggregationTopology {
                            raw_xmss: 0,
                            children: vec![
                                AggregationTopology {
                                    raw_xmss: 1400,
                                    children: vec![],
                                    log_inv_rate: 2,
                                };
                                2
                            ],
                            log_inv_rate: 2,
                        },
                    ],
                    log_inv_rate: 1,
                }],
                log_inv_rate: 4,
            };
            run_aggregation_benchmark(&topology, 5, prox_gaps_conjecture, false);
        }
    }
}
