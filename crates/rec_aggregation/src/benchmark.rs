use std::io::{self, Write};
use std::time::Instant;

use lean_vm::*;
use multilinear_toolkit::prelude::*;
use utils::pretty_integer;
use xmss::signers_cache::*;
use xmss::{XmssPublicKey, XmssSignature};

use crate::compilation::{get_aggregation_bytecode, init_aggregation_bytecode};
use crate::{AggregatedSigs, AggregationTopology, aggregate, count_signers, verify_aggregation};

fn count_nodes(topology: &AggregationTopology) -> usize {
    1 + topology.children.iter().map(count_nodes).sum::<usize>()
}

mod s {
    pub const R: &str = "\x1b[0m";
    pub const B: &str = "\x1b[1m";
    pub const D: &str = "\x1b[2m";
    pub const GRN: &str = "\x1b[38;5;114m";
    pub const RED: &str = "\x1b[38;5;167m";
    pub const ORG: &str = "\x1b[38;5;215m";
    pub const CYN: &str = "\x1b[38;5;117m";
    pub const PUR: &str = "\x1b[38;5;141m";
    pub const GRY: &str = "\x1b[38;5;242m";
    pub const WHT: &str = "\x1b[38;5;252m";
    pub const DRK: &str = "\x1b[38;5;238m";
}

#[derive(Clone)]
struct NodeStats {
    time_secs: f64,
    proof_kib: usize,
    cycles: usize,
    memory: usize,
    poseidons: usize,
    dots: usize,
    n_xmss: Option<usize>,
}

struct LiveTree {
    descs: Vec<String>,
    plain_lens: Vec<usize>,
    max_plain_len: usize,
    statuses: Vec<Option<NodeStats>>,
    n_nodes: usize,
}

impl LiveTree {
    fn new(descs: Vec<String>, plain_lens: Vec<usize>) -> Self {
        let max_plain_len = plain_lens.iter().copied().max().unwrap_or(0);
        let n_nodes = descs.len();
        Self {
            descs,
            plain_lens,
            max_plain_len,
            statuses: vec![None; n_nodes],
            n_nodes,
        }
    }

    fn header(&self) -> String {
        let pad = self.max_plain_len + 6; // desc + dots + " ▸ "
        let spacer = " ".repeat(pad);
        format!(
            "{}{}{:>10}  {:>8}  {:>10}  {:>10}  {:>10}  {:>10}{}",
            s::D,
            spacer,
            "time",
            "size",
            "cycles",
            "memory",
            "poseidons",
            "dots",
            s::R,
        )
    }

    fn format_line(&self, i: usize) -> String {
        let desc = &self.descs[i];
        let gap = self.max_plain_len + 2 - self.plain_lens[i];
        let dots = format!("{}{}{}", s::DRK, "·".repeat(gap), s::R);
        match &self.statuses[i] {
            None => desc.to_string(),
            Some(st) => {
                // Both branches produce exactly 10 visible characters.
                let time_col = match st.n_xmss {
                    Some(n) => {
                        let throughput = n as f64 / st.time_secs;
                        // " 536 sig/s" = 10 chars
                        format!("{}{}{:>4.0} sig/s{}", s::ORG, s::B, throughput, s::R)
                    }
                    // "    1.815s" = 10 chars
                    None => format!("{}{}{:>9.3}s{}", s::ORG, s::B, st.time_secs, s::R),
                };
                format!(
                    "{} {} {}▸{} {}  {}{}{:>4} KiB{}  {}{:>10}{}  {}{:>10}{}  {}{:>10}{}  {}{:>10}{}",
                    desc,
                    dots,
                    s::DRK,
                    s::R,
                    time_col,
                    s::CYN,
                    s::B,
                    st.proof_kib,
                    s::R,
                    s::WHT,
                    pretty_integer(st.cycles),
                    s::R,
                    s::WHT,
                    pretty_integer(st.memory),
                    s::R,
                    s::WHT,
                    pretty_integer(st.poseidons),
                    s::R,
                    s::WHT,
                    pretty_integer(st.dots),
                    s::R,
                )
            }
        }
    }

    fn print_initial(&self) {
        println!("{}", self.header());
        for i in 0..self.n_nodes {
            println!("{}", self.format_line(i));
        }
        println!();
        io::stdout().flush().unwrap();
    }

    fn update_node(&mut self, index: usize, stats: NodeStats) {
        self.statuses[index] = Some(stats);
        let line = self.format_line(index);
        let up = self.n_nodes + 1 - index;
        print!("\x1b[{}A\r\x1b[2K{}\x1b[{}B\r", up, line, up);
        io::stdout().flush().unwrap();
    }

    fn total_time(&self) -> f64 {
        self.statuses
            .iter()
            .filter_map(|s| s.as_ref())
            .map(|st| st.time_secs)
            .sum()
    }
}

#[allow(clippy::too_many_arguments)]
fn build_tree_descs(
    topology: &AggregationTopology,
    overlap: usize,
    prefix: &str,
    child_prefix: &str,
    plain_prefix: &str,
    plain_child_prefix: &str,
    descs: &mut Vec<String>,
    plain_lens: &mut Vec<usize>,
) {
    let n_sigs = count_signers(topology, overlap);
    let n_children = topology.children.len();
    let is_leaf = n_children == 0;

    let (icon, icon_color) = if is_leaf { ("◇", s::ORG) } else { ("◆", s::PUR) };
    let reduced = if n_children > 1 { overlap * (n_children - 1) } else { 0 };
    let children_sum: usize = topology.children.iter().map(|c| count_signers(c, overlap)).sum();
    let detail = if is_leaf {
        format!("{}{}{}", s::GRN, n_sigs, s::R)
    } else {
        let mut parts: Vec<String> = vec![];
        if children_sum > 0 {
            parts.push(format!("{}{}{}", s::GRN, children_sum, s::R));
        }
        if topology.raw_xmss > 0 {
            parts.push(format!("{}+ {}{}", s::GRN, topology.raw_xmss, s::R));
        }
        if reduced > 0 {
            parts.push(format!("{}- {}{}", s::RED, reduced, s::R));
        }
        parts.join(" ")
    };
    let plain_detail = if is_leaf {
        format!("{}", n_sigs)
    } else {
        let mut parts: Vec<String> = vec![];
        if children_sum > 0 {
            parts.push(format!("{}", children_sum));
        }
        if topology.raw_xmss > 0 {
            parts.push(format!("+ {}", topology.raw_xmss));
        }
        if reduced > 0 {
            parts.push(format!("- {}", reduced));
        }
        parts.join(" ")
    };

    // Children first (above), so leaves print at the top and proving flows top → bottom.
    for (i, child) in topology.children.iter().enumerate() {
        let is_first = i == 0;
        let (p, cp, pp, pcp) = if is_first {
            (
                format!("{}{}┌──▸{} ", child_prefix, s::PUR, s::R),
                format!("{}     ", child_prefix),
                format!("{}┌──▸ ", plain_child_prefix),
                format!("{}     ", plain_child_prefix),
            )
        } else {
            (
                format!("{}{}├──▸{} ", child_prefix, s::PUR, s::R),
                format!("{}{}│   {} ", child_prefix, s::PUR, s::R),
                format!("{}├──▸ ", plain_child_prefix),
                format!("{}│    ", plain_child_prefix),
            )
        };
        build_tree_descs(child, overlap, &p, &cp, &pp, &pcp, descs, plain_lens);
    }

    // Then the node itself (below its children).
    let inv_rate = 1 << topology.log_inv_rate;
    let rate_tag = format!(" {}R=1/{}{}", s::D, inv_rate, s::R);
    let plain_rate_tag = format!(" R=1/{}", inv_rate);
    let desc = format!("{}{}{}{} {}{}", prefix, icon_color, icon, s::R, detail, rate_tag,);
    let plain = format!("{}{} {}{}", plain_prefix, icon, plain_detail, plain_rate_tag);
    plain_lens.push(plain.chars().count());
    descs.push(desc);
}

#[allow(clippy::too_many_arguments)]
fn build_aggregation(
    topology: &AggregationTopology,
    display_index: usize,
    display: &mut LiveTree,
    pub_keys: &[XmssPublicKey],
    signatures: &[XmssSignature],
    overlap: usize,
    prox_gaps_conjecture: bool,
    tracing: bool,
) -> AggregatedSigs {
    let message = message_for_benchmark();
    let slot = BENCHMARK_SLOT;
    let raw_count = topology.raw_xmss;
    let raw_xmss: Vec<(XmssPublicKey, XmssSignature)> = (0..raw_count)
        .map(|i| (pub_keys[i].clone(), signatures[i].clone()))
        .collect();

    let mut child_results = vec![];
    let mut child_start = raw_count;
    let mut child_display_index = display_index;
    for (child_idx, child) in topology.children.iter().enumerate() {
        let child_count = count_signers(child, overlap);
        let child_agg = build_aggregation(
            child,
            child_display_index,
            display,
            &pub_keys[child_start..child_start + child_count],
            &signatures[child_start..child_start + child_count],
            overlap,
            prox_gaps_conjecture,
            tracing,
        );
        child_results.push(child_agg);
        child_display_index += count_nodes(child);
        child_start += child_count;
        if child_idx < topology.children.len() - 1 {
            child_start -= overlap;
        }
    }

    let time = Instant::now();
    let result = aggregate(
        &child_results,
        raw_xmss,
        &message,
        slot,
        topology.log_inv_rate,
        prox_gaps_conjecture,
    );
    let elapsed = time.elapsed();

    if tracing {
        println!("{}", result.metadata.display());
    }

    if !tracing {
        let own_display_index = display_index + count_nodes(topology) - 1;
        let proof_kib = result.compressed_proof_len_fe * F::bits() / (8 * 1024);
        let is_leaf = topology.children.is_empty();
        display.update_node(
            own_display_index,
            NodeStats {
                time_secs: elapsed.as_secs_f64(),
                proof_kib,
                cycles: result.metadata.cycles,
                memory: result.metadata.memory,
                poseidons: result.metadata.n_poseidons,
                dots: result.metadata.n_dot_products,
                n_xmss: if is_leaf { Some(topology.raw_xmss) } else { None },
            },
        );
    }

    result
}

pub fn run_aggregation_benchmark(
    topology: &AggregationTopology,
    overlap: usize,
    prox_gaps_conjecture: bool,
    tracing: bool,
) {
    if tracing {
        utils::init_tracing();
    }
    precompute_dft_twiddles::<F>(1 << 24);

    let n_sigs = count_signers(topology, overlap);

    let cache = read_benchmark_signers_cache();
    assert!(cache.len() >= n_sigs);
    let paired: Vec<_> = (0..n_sigs)
        .into_par_iter()
        .map(|i| reconstruct_signer_for_benchmark(i, cache[i]))
        .collect();
    let (pub_keys, signatures): (Vec<_>, Vec<_>) = paired.into_iter().unzip();

    init_aggregation_bytecode();
    println!(
        "Aggregation program: {} instructions\n",
        pretty_integer(get_aggregation_bytecode(prox_gaps_conjecture).instructions.len())
    );

    // Build display
    let mut descs = vec![];
    let mut plain_lens = vec![];
    build_tree_descs(topology, overlap, "  ", "  ", "  ", "  ", &mut descs, &mut plain_lens);
    let mut display = LiveTree::new(descs, plain_lens);

    if !tracing {
        display.print_initial();
    }

    let aggregated_sigs = build_aggregation(
        topology,
        0,
        &mut display,
        &pub_keys,
        &signatures,
        overlap,
        prox_gaps_conjecture,
        tracing,
    );

    // Verify root proof
    let message = message_for_benchmark();
    verify_aggregation(&aggregated_sigs, &message, BENCHMARK_SLOT, prox_gaps_conjecture).unwrap();
}
