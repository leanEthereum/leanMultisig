use backend::*;
use lean_vm::*;
use serde::{Deserialize, Serialize};
use std::io::{self, Write};
use std::time::Instant;
use utils::ansi as s;
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};
use xmss::{XmssPublicKey, XmssSignature};

use crate::compilation::{get_aggregation_bytecode, init_aggregation_bytecode};
use crate::{AggregatedXMSS, AggregationTopology, count_signers, xmss_aggregate};

fn count_nodes(topology: &AggregationTopology) -> usize {
    1 + topology.children.iter().map(count_nodes).sum::<usize>()
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeStats {
    pub time_secs: f64,
    pub proof_kib: usize,
    pub cycles: usize,
    pub memory: usize,
    pub poseidons: usize,
    pub dots: usize,
    pub n_xmss: Option<usize>,
}

/// Per-node metrics in tree-walk order, plus the total wall time.
///
/// `nodes[i].0` is the topology-relative path from the root (`[]` = root);
/// each element is a child index into its parent's `children` vec.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkReport {
    pub total_time_secs: f64,
    pub nodes: Vec<(Vec<usize>, NodeStats)>,
}

struct LiveTree {
    descs: Vec<String>,
    plain_lens: Vec<usize>,
    max_plain_len: usize,
    statuses: Vec<Option<NodeStats>>,
    n_nodes: usize,
    silent: bool,
}

impl LiveTree {
    fn new(descs: Vec<String>, plain_lens: Vec<usize>, silent: bool) -> Self {
        let max_plain_len = plain_lens.iter().copied().max().unwrap_or(0);
        let n_nodes = descs.len();
        Self {
            descs,
            plain_lens,
            max_plain_len,
            statuses: vec![None; n_nodes],
            n_nodes,
            silent,
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
            "extension-ops",
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
        if self.silent {
            return;
        }
        println!("{}", self.header());
        for i in 0..self.n_nodes {
            println!("{}", self.format_line(i));
        }
        println!();
        io::stdout().flush().unwrap();
    }

    fn update_node(&mut self, index: usize, stats: NodeStats) {
        self.statuses[index] = Some(stats);
        if self.silent {
            return;
        }
        let line = self.format_line(index);
        let up = self.n_nodes + 1 - index;
        print!("\x1b[{}A\r\x1b[2K{}\x1b[{}B\r", up, line, up);
        io::stdout().flush().unwrap();
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
    nodes: &mut Vec<(Vec<usize>, NodeStats)>,
    live_tree: &mut LiveTree,
    path: &mut Vec<usize>,
    pub_keys: &[XmssPublicKey],
    signatures: &[XmssSignature],
    overlap: usize,
    tracing: bool,
) -> (Vec<XmssPublicKey>, AggregatedXMSS, f64) {
    let raw_count = topology.raw_xmss;
    let raw_xmss: Vec<(XmssPublicKey, XmssSignature)> = (0..raw_count)
        .map(|i| (pub_keys[i].clone(), signatures[i].clone()))
        .collect();

    let mut child_pub_keys_list: Vec<Vec<XmssPublicKey>> = vec![];
    let mut child_aggs: Vec<AggregatedXMSS> = vec![];
    let mut child_start = raw_count;
    let mut child_display_index = display_index;
    for (child_idx, child) in topology.children.iter().enumerate() {
        let child_count = count_signers(child, overlap);
        path.push(child_idx);
        let (child_pks, child_agg, _) = build_aggregation(
            child,
            child_display_index,
            nodes,
            live_tree,
            path,
            &pub_keys[child_start..child_start + child_count],
            &signatures[child_start..child_start + child_count],
            overlap,
            tracing,
        );
        path.pop();
        child_pub_keys_list.push(child_pks);
        child_aggs.push(child_agg);
        child_display_index += count_nodes(child);
        child_start += child_count;
        if child_idx < topology.children.len() - 1 {
            child_start -= overlap;
        }
    }

    let children: Vec<(&[XmssPublicKey], AggregatedXMSS)> = child_pub_keys_list
        .iter()
        .zip(child_aggs)
        .map(|(pks, agg)| (pks.as_slice(), agg))
        .collect();

    let time = Instant::now();

    #[cfg(not(feature = "standard-alloc"))]
    zk_alloc::begin_phase();

    let (global_pub_keys, result) = xmss_aggregate(
        &children,
        raw_xmss,
        &message_for_benchmark(),
        BENCHMARK_SLOT,
        topology.log_inv_rate,
    );

    // Clone the outputs out of the arena before the next phase resets its slabs.
    #[cfg(not(feature = "standard-alloc"))]
    let (global_pub_keys, result) = {
        zk_alloc::end_phase();
        (global_pub_keys.clone(), result.clone())
    };

    let elapsed = time.elapsed();

    if tracing {
        println!("{}", result.metadata.as_ref().unwrap().display());
        if topology.children.is_empty() {
            println!(
                "{} XMSS/s",
                (topology.raw_xmss as f64 / elapsed.as_secs_f64()).round() as usize
            );
        } else {
            println!("{:.3}s the final aggregation step", elapsed.as_secs_f64());
        }
        println!(
            "Proof size: {} KiB",
            result.proof.proof_size_fe() * F::bits() / (8 * 1024)
        );
    }

    let own_display_index = display_index + count_nodes(topology) - 1;
    let proof_kib = result.proof.proof_size_fe() * F::bits() / (8 * 1024);
    let is_leaf = topology.children.is_empty();
    let stats = NodeStats {
        time_secs: elapsed.as_secs_f64(),
        proof_kib,
        cycles: result.metadata.as_ref().unwrap().cycles,
        memory: result.metadata.as_ref().unwrap().memory,
        poseidons: result.metadata.as_ref().unwrap().n_poseidons,
        dots: result.metadata.as_ref().unwrap().n_extension_ops,
        n_xmss: if is_leaf { Some(topology.raw_xmss) } else { None },
    };
    nodes.push((path.clone(), stats.clone()));
    // LiveTree shares stdout with `tracing-forest`; only paint when tracing
    // is off. (silent mode is handled inside `update_node`.)
    if !tracing {
        live_tree.update_node(own_display_index, stats);
    }

    (global_pub_keys, result, elapsed.as_secs_f64())
}

pub fn run_aggregation_benchmark(
    topology: &AggregationTopology,
    overlap: usize,
    tracing: bool,
    silent: bool,
) -> BenchmarkReport {
    // Tell macOS this is a user-initiated, latency-critical computation and
    // should not be throttled / App-Napped.
    #[cfg(target_os = "macos")]
    let _activity = macos_activity::Activity::begin("lean-multisig benchmark");

    if tracing {
        utils::init_tracing();
    }
    precompute_dft_twiddles::<F>(1 << 24);

    let n_sigs = count_signers(topology, overlap);

    let cache = get_benchmark_signatures();
    assert!(cache.len() >= n_sigs);
    let (pub_keys, signatures): (Vec<_>, Vec<_>) = cache[..n_sigs].iter().cloned().unzip();

    init_aggregation_bytecode();

    if !silent {
        println!(
            "Aggregation program: {} instructions\n",
            pretty_integer(get_aggregation_bytecode().code.len())
        );
    }

    // Build display
    let mut descs = vec![];
    let mut plain_lens = vec![];
    build_tree_descs(topology, overlap, "  ", "  ", "  ", "  ", &mut descs, &mut plain_lens);
    let mut display = LiveTree::new(descs, plain_lens, silent);

    if !tracing {
        display.print_initial();
    }

    let mut nodes: Vec<(Vec<usize>, NodeStats)> = Vec::new();
    let mut path: Vec<usize> = Vec::new();
    let (global_pub_keys, aggregated_sigs, total_time_secs) = build_aggregation(
        topology,
        0,
        &mut nodes,
        &mut display,
        &mut path,
        &pub_keys,
        &signatures,
        overlap,
        tracing,
    );

    // Verify root proof
    crate::xmss_verify_aggregation(
        &global_pub_keys,
        &aggregated_sigs,
        &message_for_benchmark(),
        BENCHMARK_SLOT,
    )
    .unwrap();

    BenchmarkReport { total_time_secs, nodes }
}

// TODO is there a better fix?
#[cfg(target_os = "macos")]
mod macos_activity {
    use objc2::rc::Retained;
    use objc2::runtime::{NSObjectProtocol, ProtocolObject};
    use objc2_foundation::{NSActivityOptions, NSProcessInfo, NSString};

    pub struct Activity {
        process_info: Retained<NSProcessInfo>,
        token: Retained<ProtocolObject<dyn NSObjectProtocol>>,
    }

    impl Activity {
        pub fn begin(reason: &str) -> Self {
            let process_info = NSProcessInfo::processInfo();
            let reason = NSString::from_str(reason);
            let options = NSActivityOptions::UserInitiated | NSActivityOptions::LatencyCritical;
            let token = process_info.beginActivityWithOptions_reason(options, &reason);
            Self { process_info, token }
        }
    }

    impl Drop for Activity {
        fn drop(&mut self) {
            unsafe { self.process_info.endActivity(&self.token) };
        }
    }
}

#[test]
#[ignore]
fn test_aggregation_throughput_per_num_xmss() {
    let log_inv_rate = 1;
    precompute_dft_twiddles::<F>(1 << 24);
    init_aggregation_bytecode();
    let _ = get_aggregation_bytecode();
    let mut num_xmss_and_time = vec![];
    let mut indexes = vec![];
    for i in 1..100 {
        indexes.push(i * 10);
    }
    for i in 50..100 {
        indexes.push(i * 20);
    }
    for i in 40..60 {
        indexes.push(i * 50);
    }
    for num_xmss in indexes {
        let topology = AggregationTopology {
            raw_xmss: num_xmss,
            children: vec![],
            log_inv_rate,
        };
        let time = run_aggregation_benchmark(&topology, 0, false, true).total_time_secs;
        num_xmss_and_time.push((num_xmss, time));
        println!(
            "{} XMSS -> {} XMSS/s",
            num_xmss,
            (num_xmss as f64 / time).round() as usize
        );

        std::thread::sleep(std::time::Duration::from_millis(1000));

        let mut csv = String::from("num_sigs,throughput (XMSS/s)\n");
        for &(n, t) in &num_xmss_and_time {
            csv.push_str(&format!("{},{:.1}\n", n, n as f64 / t));
        }
        let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benchmarks/xmss_throughput.csv");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, &csv).unwrap();
        println!("\nWrote {}", path.display());
    }
}
