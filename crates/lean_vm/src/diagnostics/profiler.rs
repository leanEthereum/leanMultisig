use backend::pretty_integer;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::Range;

use crate::core::{Label, MemoryAddress, SourceLocation};
use crate::stack_trace::find_function_for_location;
use crate::{ExecutionHistory, NONRESERVED_PROGRAM_INPUT_START};

pub(crate) fn profiling_report(
    instructions: &ExecutionHistory,
    function_locations: &BTreeMap<SourceLocation, String>,
    mem_profile: &MemoryProfile,
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

    for (&location, &cycle_count) in instructions.lines.iter().zip(&instructions.lines_cycles) {
        let (_, current_function_name) = find_function_for_location(location, function_locations);

        if prev_function_name != current_function_name {
            if let Some(pos) = call_stack.iter().position(|f| f == &current_function_name) {
                while call_stack.len() > pos + 1 {
                    call_stack.pop();
                }
            } else {
                // New function call
                call_stack.push(current_function_name.clone());
                let stats = function_stats.entry(current_function_name.clone()).or_default();
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

    // memory profiling report
    report += &memory_profiling_report(mem_profile);

    report.push_str("\n╔═════════════════════════════════════════════════════════════════════════╗\n");
    report.push_str("║                              PROFILING REPORT                           ║\n");
    report.push_str("╚═════════════════════════════════════════════════════════════════════════╝\n\n");

    report.push_str("──────────────────────────────────────────────────────────────────────────\n");
    report.push_str("      │      Exclusive      │      Inclusive      │                       \n");
    report.push_str("Calls │  Cycles  ┊ Avg/Call │  Cycles  ┊ Avg/Call │ Function Name         \n");
    report.push_str("──────────────────────────────────────────────────────────────────────────\n");

    for (func_name, stats) in &function_data {
        let avg_exclusive = stats.exclusive_cycles.checked_div(stats.call_count).unwrap_or(0);

        let avg_inclusive = stats.inclusive_cycles.checked_div(stats.call_count).unwrap_or(0);

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

#[derive(Debug, Clone)]
pub enum MemoryObjectType {
    StackFrame,
    NonVectorHeapObject,
    VectorHeapObject,
}

/// An object (i.e., stack frame or heap object) in the memory profile
#[derive(Debug, Clone)]
pub struct MemoryObject {
    pub object_type: MemoryObjectType,

    /// The name of the function allocating this object
    pub function_name: Label,

    /// The number of words in this stack frame
    pub size: usize,
}

/// Struct to accumulate memory profiling results
#[derive(Debug, Clone)]
pub struct MemoryProfile {
    /// The set of used memory addresses
    pub used: BTreeSet<MemoryAddress>,

    /// The range of public input addresses
    pub public_inputs: Range<MemoryAddress>,

    /// The range of private input addresses
    pub private_inputs: Range<MemoryAddress>,

    /// The memory objects keyed by their start addresses
    pub objects: BTreeMap<MemoryAddress, MemoryObject>,
}

pub(crate) fn memory_profiling_report(profile: &MemoryProfile) -> String {
    let mut report = String::new();

    let f_allocations = function_allocations(profile);
    let all_allocated_mem = all_allocated_memory(profile);
    let footprint = all_allocated_mem.last().unwrap() + 1;
    let allocated = all_allocated_mem.len();
    let allocated_percent = (allocated as f64 / footprint as f64) * 100.0;
    let used = profile.used.len();
    let used_but_not_allocated = count_used_but_not_allocated(&profile.used, &all_allocated_mem);
    let used_but_not_allocated_percent = (used_but_not_allocated as f64 / footprint as f64) * 100.0;
    let allocated_but_not_used = count_allocated_but_not_used(&profile.used, &all_allocated_mem);
    let allocated_but_not_used_percent = (allocated_but_not_used as f64 / allocated as f64) * 100.0;

    // TODO: add percentages used
    report.push_str("============================================\n");
    report.push_str("=        DETAILED MEMORY PROFILING         =\n");
    report.push_str("============================================\n");
    report.push('\n');
    report.push_str(&format!("Total memory footprint: {}\n", pretty_integer(footprint)));
    report.push_str(&format!(
        "Total allocated memory: {} ({:.2}% of footprint)\n",
        pretty_integer(allocated),
        allocated_percent
    ));
    report.push_str(&format!("Total used memory: {}\n", pretty_integer(used)));
    report.push_str(&format!(
        "Total used but not allocated: {} ({:.2}% of footprint)\n",
        pretty_integer(used_but_not_allocated),
        used_but_not_allocated_percent
    ));
    report.push_str(&format!(
        "Total allocated but not used: {} ({:.2}% of allocated)\n\n",
        pretty_integer(allocated_but_not_used),
        allocated_but_not_used_percent
    ));

    for (function_name, f_allocations) in f_allocations {
        let FunctionAllocationStats {
            frame_words_allocated,
            frame_words_used,
            heap_nonvector_words_allocated,
            heap_nonvector_words_used,
            heap_vector_words_allocated,
            heap_vector_words_used,
        } = function_allocation_stats(&profile.used, &f_allocations);
        report.push_str(&format!("Function {function_name}:\n"));
        report.push_str(&format!(
            " * Frame words allocated: {}\n",
            pretty_integer(frame_words_allocated)
        ));
        report.push_str(&format!(
            " * Frame words used: {} ({:.2}%)\n",
            pretty_integer(frame_words_used),
            (frame_words_used as f64 / frame_words_allocated as f64) * 100.0
        ));
        report.push_str(&format!(
            " * Non-vector heap words allocated: {}\n",
            pretty_integer(heap_nonvector_words_allocated)
        ));
        report.push_str(&format!(
            " * Non-vector heap words used: {} ({:.2}%)\n",
            pretty_integer(heap_nonvector_words_used),
            (heap_nonvector_words_used as f64 / heap_nonvector_words_allocated as f64) * 100.0
        ));
        report.push_str(&format!(
            " * Vector heap words allocated: {}\n",
            pretty_integer(heap_vector_words_allocated)
        ));
        report.push_str(&format!(
            " * Vector heap words used: {} ({:.2}%)\n\n",
            pretty_integer(heap_vector_words_used),
            (heap_vector_words_used as f64 / heap_vector_words_allocated as f64) * 100.0
        ));
    }

    report
}

fn function_allocations(profile: &MemoryProfile) -> BTreeMap<Label, BTreeMap<MemoryAddress, MemoryObject>> {
    let mut allocations = BTreeMap::new();

    for (addr, object) in profile.objects.iter() {
        let objects = if let Some(objects) = allocations.get_mut(&object.function_name) {
            objects
        } else {
            allocations.insert(object.function_name.clone(), BTreeMap::new());
            allocations.get_mut(&object.function_name).unwrap()
        };
        objects.insert(*addr, object.clone());
    }

    allocations
}

#[derive(Debug, Clone, Default)]
struct FunctionAllocationStats {
    frame_words_allocated: usize,
    frame_words_used: usize,
    heap_nonvector_words_allocated: usize,
    heap_nonvector_words_used: usize,
    heap_vector_words_allocated: usize,
    heap_vector_words_used: usize,
}

/// Get the allocation stats for a particular function.
fn function_allocation_stats(
    used: &BTreeSet<MemoryAddress>,
    function_allocations: &BTreeMap<MemoryAddress, MemoryObject>,
) -> FunctionAllocationStats {
    let mut stats = FunctionAllocationStats::default();

    for (object_address, object) in function_allocations.iter() {
        let address_range = *object_address..*object_address + object.size;
        let object_words_used = used.range(address_range).count();

        match object.object_type {
            MemoryObjectType::StackFrame => {
                stats.frame_words_allocated += object.size;
                stats.frame_words_used += object_words_used;
            }
            MemoryObjectType::NonVectorHeapObject => {
                stats.heap_nonvector_words_allocated += object.size;
                stats.heap_nonvector_words_used += object_words_used;
            }
            MemoryObjectType::VectorHeapObject => {
                stats.heap_vector_words_allocated += object.size;
                stats.heap_vector_words_used += object_words_used;
            }
        }
    }

    stats
}

/// Get the set of all allocated memory addresses, including public and private input regions.
fn all_allocated_memory(profile: &MemoryProfile) -> BTreeSet<MemoryAddress> {
    let mut result = BTreeSet::new();

    // Reserved public inputs
    for addr in 0..NONRESERVED_PROGRAM_INPUT_START {
        result.insert(addr);
    }

    // Non-reserved public inputs
    for addr in profile.public_inputs.clone() {
        result.insert(addr);
    }

    // Private inputs
    for addr in profile.private_inputs.clone() {
        result.insert(addr);
    }

    // Stack and heap objects
    for (start_addr, object) in profile.objects.iter() {
        for addr in *start_addr..start_addr + object.size {
            result.insert(addr);
        }
    }

    result
}

/// Get the number of used memory addresses which are not allocated.
fn count_used_but_not_allocated(used: &BTreeSet<MemoryAddress>, allocated: &BTreeSet<MemoryAddress>) -> usize {
    let diff = BTreeSet::from_iter(used.difference(allocated));
    let len = diff.len();
    if len > 0 {
        println!("!! Addresses defined but not used:");
        for addr in diff {
            println!("{addr}");
        }
    }
    len
}

/// Get the number of allocated memory addresses which are not used.
fn count_allocated_but_not_used(used: &BTreeSet<MemoryAddress>, allocated: &BTreeSet<MemoryAddress>) -> usize {
    allocated.difference(used).count()
}
