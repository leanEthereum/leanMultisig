use clap::Parser;
use rec_aggregation::{AggregationTopology, benchmark::run_aggregation_benchmark, biggest_leaf};

#[cfg(not(feature = "standard-alloc"))]
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

fn run_with_warmup(topology: &AggregationTopology, overlap: usize, tracing: bool, repeat: usize) {
    let warmup = biggest_leaf(topology).unwrap();
    println!("warming up...");
    let _ = run_aggregation_benchmark(&warmup, 0, false, true);
    for i in 0..repeat {
        let t = run_aggregation_benchmark(topology, overlap, tracing, false);
        if repeat > 1 {
            eprintln!("proof {}/{repeat}: {t:.3}s", i + 1);
        }
    }
}

fn main() {
    #[cfg(not(feature = "standard-alloc"))]
    zk_alloc::init();

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
            run_with_warmup(&topology, 0, tracing, repeat);
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
                        raw_xmss: 750,
                        children: vec![],
                        log_inv_rate,
                    };
                    n
                ],
                log_inv_rate,
            };
            run_with_warmup(&topology, 0, tracing, repeat);
        }
        Cli::FancyAggregation { repeat } => {
            let topology = AggregationTopology {
                raw_xmss: 0,
                children: vec![AggregationTopology {
                    raw_xmss: 10,
                    children: vec![
                        AggregationTopology {
                            raw_xmss: 25,
                            children: vec![
                                AggregationTopology {
                                    raw_xmss: 1550,
                                    children: vec![],
                                    log_inv_rate: 1,
                                };
                                3
                            ],
                            log_inv_rate: 1,
                        },
                        AggregationTopology {
                            raw_xmss: 0,
                            children: vec![
                                AggregationTopology {
                                    raw_xmss: 775,
                                    children: vec![],
                                    log_inv_rate: 2,
                                };
                                2
                            ],
                            log_inv_rate: 2,
                        },
                    ],
                    log_inv_rate: 2,
                }],
                log_inv_rate: 4,
            };
            run_with_warmup(&topology, 5, false, repeat);
        }
    }
}
