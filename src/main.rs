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
        #[arg(
            long,
            help = "Print BenchmarkReport as JSON on stdout (one line per run); suppresses live output"
        )]
        json: bool,
    },
    #[command(about = "Run n->1 recursion")]
    Recursion {
        #[arg(long, default_value = "2", help = "Number of recursive proofs to aggregate")]
        n: usize,
        #[arg(long, help = "log(1/rate) in WHIR", default_value = "2", short = 'r')]
        log_inv_rate: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
        #[arg(
            long,
            help = "Print BenchmarkReport as JSON on stdout (one line per run); suppresses live output"
        )]
        json: bool,
    },
    #[command(about = "Run a fancy aggregation topology")]
    FancyAggregation {
        #[arg(
            long,
            help = "Print BenchmarkReport as JSON on stdout (one line per run); suppresses live output"
        )]
        json: bool,
    },
}

fn run_with_warmup(topology: &AggregationTopology, tracing: bool, json: bool) {
    let warmup = biggest_leaf(topology).unwrap();
    eprint!("warming up... ");
    let _ = run_aggregation_benchmark(&warmup, false, true);
    eprintln!(
        "used {:.2} GiB",
        system_info::peak_rss_bytes() as f64 / (1u64 << 30) as f64
    );
    let report = run_aggregation_benchmark(topology, tracing && !json, json);
    if json {
        println!("{}", serde_json::to_string(&report).unwrap());
    }
}

#[allow(clippy::too_many_lines)]
fn main() {
    #[cfg(not(feature = "standard-alloc"))]
    zk_alloc::init();

    let cli = Cli::parse();

    match cli {
        Cli::Xmss {
            n_signatures,
            log_inv_rate,
            tracing,
            json,
        } => {
            let topology = AggregationTopology {
                raw_xmss: n_signatures,
                children: vec![],
                log_inv_rate,
                overlap: 0,
            };
            run_with_warmup(&topology, tracing, json);
        }
        Cli::Recursion {
            n,
            log_inv_rate,
            tracing,
            json,
        } => {
            let topology = AggregationTopology {
                raw_xmss: 0,
                children: vec![
                    AggregationTopology {
                        raw_xmss: 700,
                        children: vec![],
                        log_inv_rate,
                        overlap: 0,
                    };
                    n
                ],
                log_inv_rate,
                overlap: 0,
            };
            run_with_warmup(&topology, tracing, json);
        }
        Cli::FancyAggregation { json } => {
            let topology = AggregationTopology {
                raw_xmss: 0,
                children: vec![AggregationTopology {
                    raw_xmss: 10,
                    children: vec![
                        AggregationTopology {
                            raw_xmss: 25,
                            children: vec![
                                AggregationTopology {
                                    raw_xmss: 0,
                                    children: vec![
                                        AggregationTopology {
                                            raw_xmss: 1400,
                                            children: vec![],
                                            log_inv_rate: 1,
                                            overlap: 0,
                                        },
                                        AggregationTopology {
                                            raw_xmss: 658,
                                            children: vec![],
                                            log_inv_rate: 2,
                                            overlap: 0,
                                        },
                                    ],
                                    log_inv_rate: 2,
                                    overlap: 10,
                                },
                                AggregationTopology {
                                    raw_xmss: 0,
                                    children: vec![
                                        AggregationTopology {
                                            raw_xmss: 1400,
                                            children: vec![],
                                            log_inv_rate: 2,
                                            overlap: 0,
                                        },
                                        AggregationTopology {
                                            raw_xmss: 658,
                                            children: vec![],
                                            log_inv_rate: 2,
                                            overlap: 0,
                                        },
                                    ],
                                    log_inv_rate: 2,
                                    overlap: 10,
                                },
                            ],
                            log_inv_rate: 1,
                            overlap: 5,
                        },
                        AggregationTopology {
                            raw_xmss: 0,
                            children: vec![
                                AggregationTopology {
                                    raw_xmss: 700,
                                    children: vec![],
                                    log_inv_rate: 2,
                                    overlap: 0,
                                };
                                2
                            ],
                            log_inv_rate: 2,
                            overlap: 5,
                        },
                    ],
                    log_inv_rate: 2,
                    overlap: 2,
                }],
                log_inv_rate: 4,
                overlap: 0,
            };
            run_with_warmup(&topology, false, json);
        }
    }
}
