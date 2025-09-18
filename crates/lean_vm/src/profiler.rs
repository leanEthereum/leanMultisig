use std::collections::BTreeMap;
use std::collections::HashMap;

use utils::pretty_integer;

use crate::ExecutionHistory;
use crate::stack_trace::find_function_for_line;

pub(crate) fn profiling_report(
    instructions: &ExecutionHistory,
    function_locations: &BTreeMap<usize, String>,
) -> String {
    #[derive(Default, Clone)]
    struct FunctionStats {
        call_count: usize,
        exclusive_cycles: usize, // Cycles spent in this function only
        inclusive_cycles: usize, // Cycles including all called functions
    }

    let mut function_stats: HashMap<String, FunctionStats> = HashMap::new();
    let mut call_stack: Vec<String> = Vec::new();
    let mut prev_function_name = String::new();

    for (&line_num, &cycle_count) in instructions.lines.iter().zip(&instructions.cycles) {
        let (_, current_function_name) = find_function_for_line(line_num, function_locations);

        if prev_function_name != current_function_name {
            if let Some(pos) = call_stack.iter().position(|f| f == &current_function_name) {
                while call_stack.len() > pos + 1 {
                    call_stack.pop();
                }
            } else {
                // New function call
                call_stack.push(current_function_name.clone());
                let stats = function_stats
                    .entry(current_function_name.clone())
                    .or_default();
                stats.call_count += 1;
            }
            prev_function_name = current_function_name.clone();
        }

        if let Some(top_function) = call_stack.last() {
            let stats = function_stats.entry(top_function.clone()).or_default();
            stats.exclusive_cycles += cycle_count;
        }

        for func_name in &call_stack {
            let stats = function_stats.entry(func_name.clone()).or_default();
            stats.inclusive_cycles += cycle_count;
        }
    }

    let mut function_data: Vec<(String, FunctionStats)> = function_stats.into_iter().collect();

    function_data.sort_by_key(|(_, stats)| stats.exclusive_cycles);

    let mut report = String::new();

    report
        .push_str("╔═════════════════════════════════════════════════════════════════════════╗\n");
    report
        .push_str("║                              PROFILING REPORT                           ║\n");
    report.push_str(
        "╚═════════════════════════════════════════════════════════════════════════╝\n\n",
    );

    report.push_str("──────────────────────────────────────────────────────────────────────────\n");
    report.push_str("      │      Exclusive      │      Inclusive      │                       \n");
    report.push_str("Calls │  Cycles  ┊ Avg/Call │  Cycles  ┊ Avg/Call │ Function Name         \n");
    report.push_str("──────────────────────────────────────────────────────────────────────────\n");

    for (func_name, stats) in &function_data {
        let avg_exclusive = if stats.call_count > 0 {
            stats.exclusive_cycles / stats.call_count
        } else {
            0
        };

        let avg_inclusive = if stats.call_count > 0 {
            stats.inclusive_cycles / stats.call_count
        } else {
            0
        };

        report.push_str(&format!(
            "{:>5} │ {:>8} ┊ {:>8} │ {:>8} ┊ {:>8} │ {}\n",
            pretty_integer(stats.call_count),
            pretty_integer(stats.exclusive_cycles),
            pretty_integer(avg_exclusive),
            pretty_integer(stats.inclusive_cycles),
            pretty_integer(avg_inclusive),
            func_name,
        ));
    }

    report.push_str("──────────────────────────────────────────────────────────────────────────\n");

    report
}
