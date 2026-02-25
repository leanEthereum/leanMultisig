use std::collections::BTreeMap;

use crate::core::F;
use crate::diagnostics::profiler::MemoryProfile;
use crate::execution::Memory;
use crate::{N_TABLES, Table, TableTrace};
use utils::pretty_integer;

#[derive(Debug, Default, Clone)]
pub struct ExecutionMetadata {
    pub cycles: usize,
    pub memory: usize,
    pub n_poseidons: usize,
    pub n_extension_ops: usize,
    pub bytecode_size: usize,
    pub public_input_size: usize,
    pub private_input_size: usize,
    pub runtime_memory: usize,
    pub memory_usage_percent: f64,
    pub n_poseidon_precomputed_used: usize,
    pub n_poseidons_precomputed_total: usize,
    pub stdout: String,
    pub profiling_report: Option<String>,
}

impl ExecutionMetadata {
    pub fn display(&self) -> String {
        let mut out = String::new();

        if let Some(ref report) = self.profiling_report {
            out.push_str(report);
        }

        if !self.stdout.is_empty() {
            out.push_str("╔═════════════════════════════════════════════════════════════════════════╗\n");
            out.push_str("║                                STD-OUT                                  ║\n");
            out.push_str("╚═════════════════════════════════════════════════════════════════════════╝\n");
            out.push_str(&format!("\n{}", self.stdout));
            out.push_str("──────────────────────────────────────────────────────────────────────────\n\n");
        }

        out.push_str("╔═════════════════════════════════════════════════════════════════════════╗\n");
        out.push_str("║                                 STATS                                   ║\n");
        out.push_str("╚═════════════════════════════════════════════════════════════════════════╝\n\n");

        out.push_str(&format!("CYCLES: {}\n", pretty_integer(self.cycles)));
        out.push_str(&format!("MEMORY: {}\n", pretty_integer(self.memory)));
        out.push('\n');
        out.push_str(&format!("Bytecode size: {}\n", pretty_integer(self.bytecode_size)));
        out.push_str(&format!(
            "Public input size: {}\n",
            pretty_integer(self.public_input_size)
        ));
        out.push_str(&format!(
            "Private input size: {}\n",
            pretty_integer(self.private_input_size)
        ));
        out.push_str(&format!("Runtime memory: {}\n", pretty_integer(self.runtime_memory)));
        out.push_str(&format!("Memory usage: {:.1}%\n", self.memory_usage_percent));
        out.push_str(&format!(
            "Poseidon16 precomputed used: {}/{}\n",
            pretty_integer(self.n_poseidon_precomputed_used),
            pretty_integer(self.n_poseidons_precomputed_total)
        ));
        out.push('\n');
        if self.n_poseidons > 0 {
            out.push_str(&format!(
                "Poseidon16 calls: {} (1 poseidon per {} instructions)\n",
                pretty_integer(self.n_poseidons),
                self.cycles / self.n_poseidons
            ));
        }
        if self.n_extension_ops > 0 {
            out.push_str(&format!(
                "ExtensionOp calls: {}\n",
                pretty_integer(self.n_extension_ops)
            ));
        }
        out.push_str("──────────────────────────────────────────────────────────────────────────\n");

        out
    }
}

#[derive(Debug)]
pub struct ExecutionResult {
    pub no_vec_runtime_memory: usize,
    pub public_memory_size: usize,
    pub memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
    pub traces: BTreeMap<Table, TableTrace>,
    pub metadata: ExecutionMetadata,
}

impl ExecutionResult {
    pub fn n_cycles(&self) -> usize {
        self.pcs.len()
    }
}
