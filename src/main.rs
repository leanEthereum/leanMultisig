use clap::Parser;
use rec_aggregation::{AggregationTopology, benchmark::run_aggregation_benchmark};

#[cfg(feature = "zkalloc")]
#[global_allocator]
static ALLOC: zk_alloc::ZkAllocator = zk_alloc::ZkAllocator;

#[derive(Parser)]
enum Cli {
    #[command(about = "Aggregate XMSS")]
    Xmss {
        #[arg(long)]
        n_signatures: usize,
        #[arg(long, help = "log(1/rate) in WHIR", default_value = "1", short = 'r')]
        log_inv_rate: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
        #[arg(long, help = "Number of sequential proofs to run", default_value = "1")]
        repeat: usize,
    },
    #[command(about = "Run n->1 recursion")]
    Recursion {
        #[arg(long, default_value = "2", help = "Number of recursive proofs to aggregate")]
        n: usize,
        #[arg(long, help = "log(1/rate) in WHIR", default_value = "2", short = 'r')]
        log_inv_rate: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
        #[arg(long, help = "Number of sequential proofs to run", default_value = "1")]
        repeat: usize,
    },
    #[command(about = "Run a fancy aggregation topology")]
    FancyAggregation {
        #[arg(long, help = "Number of sequential proofs to run", default_value = "1")]
        repeat: usize,
    },
}

fn main() {
    #[cfg(feature = "zkalloc")]
    zk_alloc::phase_boundary();

    let cli = Cli::parse();

    match cli {
        Cli::Xmss {
            n_signatures,
            log_inv_rate,
            tracing,
            repeat,
        } => {
            let topology = AggregationTopology {
                raw_xmss: n_signatures,
                children: vec![],
                log_inv_rate,
            };
            for i in 0..repeat {
                let t = run_aggregation_benchmark(&topology, 0, tracing);
                if repeat > 1 {
                    eprintln!("proof {}/{repeat}: {t:.3}s", i + 1);
                }
            }
        }
        Cli::Recursion {
            n,
            log_inv_rate,
            tracing,
            repeat,
        } => {
            let topology = AggregationTopology {
                raw_xmss: 0,
                children: vec![
                    AggregationTopology {
                        raw_xmss: 700,
                        children: vec![],
                        log_inv_rate,
                    };
                    n
                ],
                log_inv_rate,
            };
            for i in 0..repeat {
                let t = run_aggregation_benchmark(&topology, 0, tracing);
                if repeat > 1 {
                    eprintln!("proof {}/{repeat}: {t:.3}s", i + 1);
                }
            }
        }
        Cli::FancyAggregation { repeat } => {
            let topology = AggregationTopology {
                raw_xmss: 0,
                children: vec![AggregationTopology {
                    raw_xmss: 0,
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
                }],
                log_inv_rate: 4,
            };
            for i in 0..repeat {
                let t = run_aggregation_benchmark(&topology, 5, false);
                if repeat > 1 {
                    eprintln!("proof {}/{repeat}: {t:.3}s", i + 1);
                }
            }
        }
    }
}
