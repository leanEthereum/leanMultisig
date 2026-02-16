//! Bytecode representation and management

use multilinear_toolkit::prelude::EFPacking;
use p3_util::log2_ceil_usize;
use utils::pretty_integer;

use crate::{CodeAddress, EF, F, FileId, FunctionName, Hint, MemOrConstant, MemOrFp, Operation, SourceLocation, Table};

use super::Instruction;
use std::collections::{BTreeMap, HashMap};
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bytecode {
    pub instructions: Vec<Instruction>,
    pub instructions_multilinear: Vec<F>,
    pub instructions_multilinear_packed: Vec<EFPacking<EF>>, // embedded in the extension field(bad, TODO)
    pub hints: BTreeMap<CodeAddress, Vec<Hint>>,             // pc -> hints
    pub starting_frame_memory: usize,
    // debug
    pub function_locations: BTreeMap<SourceLocation, FunctionName>,
    pub filepaths: BTreeMap<FileId, String>,
    pub source_code: BTreeMap<FileId, String>,
    /// Maps each pc to its source location (for error reporting)
    pub pc_to_location: Vec<SourceLocation>,
}

#[derive(Default)]
struct OpcodeStats {
    add_subtypes: HashMap<&'static str, usize>,
    mul_subtypes: HashMap<&'static str, usize>,
    derefs: usize,
    cond_jumps: usize,
    uncond_jumps: usize,
    poseidons: usize,
    dot_products: usize,
}

fn computation_subtype(arg_a: &MemOrConstant, arg_c: &MemOrFp, res: &MemOrConstant) -> &'static str {
    match (arg_a, arg_c, res) {
        (MemOrConstant::MemoryAfterFp { .. }, MemOrFp::MemoryAfterFp { .. }, MemOrConstant::MemoryAfterFp { .. }) => {
            "MEM op MEM = MEM"
        }
        (MemOrConstant::MemoryAfterFp { .. }, MemOrFp::MemoryAfterFp { .. }, MemOrConstant::Constant(_)) => {
            "MEM op MEM = CONST"
        }
        (MemOrConstant::MemoryAfterFp { .. }, MemOrFp::Fp, MemOrConstant::MemoryAfterFp { .. }) => "MEM op FP = MEM",
        (MemOrConstant::MemoryAfterFp { .. }, MemOrFp::Fp, MemOrConstant::Constant(_)) => "MEM op FP = CONST",
        (MemOrConstant::Constant(_), MemOrFp::MemoryAfterFp { .. }, MemOrConstant::MemoryAfterFp { .. }) => {
            "CONST op MEM = MEM"
        }
        (MemOrConstant::Constant(_), MemOrFp::MemoryAfterFp { .. }, MemOrConstant::Constant(_)) => {
            "CONST op MEM = CONST"
        }
        (MemOrConstant::Constant(_), MemOrFp::Fp, MemOrConstant::MemoryAfterFp { .. }) => "CONST op FP = MEM",
        (MemOrConstant::Constant(_), MemOrFp::Fp, MemOrConstant::Constant(_)) => "CONST op FP = CONST",
    }
}

impl OpcodeStats {
    fn total(&self) -> usize {
        let adds: usize = self.add_subtypes.values().sum();
        let muls: usize = self.mul_subtypes.values().sum();
        adds + muls + self.derefs + self.cond_jumps + self.uncond_jumps + self.poseidons + self.dot_products
    }

    fn tally(&mut self, instruction: &Instruction) {
        match instruction {
            Instruction::Computation {
                operation: Operation::Add,
                arg_a,
                arg_c,
                res,
            } => {
                *self
                    .add_subtypes
                    .entry(computation_subtype(arg_a, arg_c, res))
                    .or_default() += 1
            }
            Instruction::Computation {
                operation: Operation::Mul,
                arg_a,
                arg_c,
                res,
            } => {
                *self
                    .mul_subtypes
                    .entry(computation_subtype(arg_a, arg_c, res))
                    .or_default() += 1
            }
            Instruction::Deref { .. } => self.derefs += 1,
            Instruction::Jump {
                condition: MemOrConstant::MemoryAfterFp { .. },
                ..
            } => self.cond_jumps += 1,
            Instruction::Jump {
                condition: MemOrConstant::Constant(_),
                ..
            } => self.uncond_jumps += 1,
            Instruction::Precompile {
                table: Table::Poseidon16(_),
                ..
            } => self.poseidons += 1,
            Instruction::Precompile {
                table: Table::DotProduct(_),
                ..
            } => self.dot_products += 1,
            Instruction::Precompile {
                table: Table::Execution(_),
                ..
            } => unreachable!(),
        }
    }

    fn pct(count: usize, total: usize) -> f64 {
        count as f64 / total as f64 * 100.0
    }

    fn print_subtypes(indent: &str, op: &str, subtypes: &HashMap<&str, usize>, total: usize) {
        let mut entries: Vec<_> = subtypes.iter().collect();
        entries.sort_by(|a, b| b.1.cmp(a.1));
        for (key, count) in entries {
            let label = key.replace("op", op);
            println!(
                "{indent}  {label}: {} ({:.1}%)",
                pretty_integer(*count),
                Self::pct(*count, total)
            );
        }
    }

    fn print(&self, indent: &str, total: usize) {
        let adds: usize = self.add_subtypes.values().sum();
        let muls: usize = self.mul_subtypes.values().sum();
        println!(
            "{indent}ADD: {} ({:.1}%)  MUL: {} ({:.1}%)  DEREF: {} ({:.1}%)  JUMP: {} ({:.1}%) (cond {}, uncond {})  Poseidon: {} ({:.1}%)  DotProd: {} ({:.1}%)",
            pretty_integer(adds),
            Self::pct(adds, total),
            pretty_integer(muls),
            Self::pct(muls, total),
            pretty_integer(self.derefs),
            Self::pct(self.derefs, total),
            pretty_integer(self.cond_jumps + self.uncond_jumps),
            Self::pct(self.cond_jumps + self.uncond_jumps, total),
            pretty_integer(self.cond_jumps),
            pretty_integer(self.uncond_jumps),
            pretty_integer(self.poseidons),
            Self::pct(self.poseidons, total),
            pretty_integer(self.dot_products),
            Self::pct(self.dot_products, total),
        );
        Self::print_subtypes(indent, "+", &self.add_subtypes, total);
        Self::print_subtypes(indent, "*", &self.mul_subtypes, total);
    }
}

impl Bytecode {
    pub fn size(&self) -> usize {
        self.instructions.len()
    }

    pub fn padded_size(&self) -> usize {
        self.size().next_power_of_two()
    }

    pub fn log_size(&self) -> usize {
        log2_ceil_usize(self.size())
    }

    /// Print instruction statistics weighted by execution multiplicity.
    /// `pcs` is the list of program counters from the execution trace (one per cycle).
    pub fn print_analytics(&self, pcs: &[usize]) {
        let mut global = OpcodeStats::default();
        for &pc in pcs {
            global.tally(&self.instructions[pc]);
        }
        println!("Execution analytics ({} cycles):", pretty_integer(pcs.len()));
        global.print("  ", pcs.len());
    }
}

impl Display for Bytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (pc, instruction) in self.instructions.iter().enumerate() {
            for hint in self.hints.get(&pc).unwrap_or(&Vec::new()) {
                writeln!(f, "hint: {hint}")?;
            }
            writeln!(f, "{pc:>4}: {instruction}")?;
        }
        Ok(())
    }
}
