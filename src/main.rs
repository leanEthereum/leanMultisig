use clap::Parser;
use rec_aggregation::{AggregationTopology, benchmark::run_aggregation_benchmark};

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
    },
    #[command(about = "Run n->1 recursion")]
    Recursion {
        #[arg(long, default_value = "2", help = "Number of recursive proofs to aggregate")]
        n: usize,
        #[arg(long, help = "log(1/rate) in WHIR", default_value = "2", short = 'r')]
        log_inv_rate: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
    },
    #[command(about = "Run a fancy aggregation topology")]
    FancyAggregation {},
}

fn main() {
    let cli = Cli::parse();

    match cli {
        Cli::Xmss {
            n_signatures,
            log_inv_rate,
            tracing,
        } => {
            let topology = AggregationTopology {
                raw_xmss: n_signatures,
                children: vec![],
                log_inv_rate,
            };
            run_aggregation_benchmark(&topology, 0, tracing);
        }
        Cli::Recursion {
            n,
            log_inv_rate,
            tracing,
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
            run_aggregation_benchmark(&topology, 0, tracing);
        }
        Cli::FancyAggregation {} => {
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
            run_aggregation_benchmark(&topology, 5, false);
        }
    }
}
