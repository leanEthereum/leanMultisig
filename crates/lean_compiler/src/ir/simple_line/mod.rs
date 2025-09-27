//! SimpleLine instruction types and implementations.

pub mod assignment;
pub mod branch;
pub mod counter_hint;
pub mod decompose_bits;
pub mod dynamic_alloc;
pub mod function_call;
pub mod location_report;
pub mod match_instr;
pub mod panic;
pub mod precompile_op;
pub mod print;
pub mod raw_memory_access;
pub mod return_instr;
pub mod static_alloc;

use crate::{
    ir::{
        IntermediateInstruction, IntermediateValue,
        compiler::{Compile, CompileContext, CompileResult, Compiler, FindInternalVars},
    },
    lang::Var,
};
use lean_vm::Label;
use std::{
    collections::BTreeSet,
    fmt::{Display, Formatter},
};

/// Trait for displaying instructions with proper indentation.
pub trait IndentedDisplay: Display {
    /// Returns a string representation with the specified indentation level.
    ///
    /// Default implementation just adds indentation to the Display output.
    fn to_string_with_indent(&self, indent: usize) -> String {
        format!("{}{}", "    ".repeat(indent), self)
    }
}

pub use assignment::Assignment;
pub use branch::Branch;
pub use counter_hint::CounterHint;
pub use decompose_bits::DecomposeBits;
pub use dynamic_alloc::DynamicAlloc;
pub use function_call::FunctionCall;
pub use location_report::LocationReport;
pub use match_instr::Match;
pub use panic::Panic;
pub use precompile_op::PrecompileOp;
pub use print::Print;
pub use raw_memory_access::RawMemoryAccess;
pub use return_instr::Return;
pub use static_alloc::StaticAlloc;

/// Simplified language instruction representation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SimpleLine {
    /// Pattern matching with computed jumps
    Match(Match),
    /// Variable assignment with binary operations
    Assignment(Assignment),
    /// Direct memory access operations
    RawMemoryAccess(RawMemoryAccess),
    /// Conditional branching (if-not-zero)
    Branch(Branch),
    /// Function invocation with argument passing
    FunctionCall(FunctionCall),
    /// Function return with values
    Return(Return),
    /// Precompiled cryptographic operations
    Precompile(PrecompileOp),
    /// Unconditional program termination
    Panic(Panic),
    /// Bit decomposition for field elements
    DecomposeBits(DecomposeBits),
    /// Counter value hint for loops
    CounterHint(CounterHint),
    /// Debug print statement
    Print(Print),
    /// Dynamic memory allocation
    DynamicAlloc(DynamicAlloc),
    /// Static compile-time memory allocation
    StaticAlloc(StaticAlloc),
    /// Source location tracking for debugging
    LocationReport(LocationReport),
}

impl Compile for SimpleLine {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        remaining_lines: &[SimpleLine],
    ) -> CompileResult {
        match self {
            SimpleLine::Match(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::Assignment(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::RawMemoryAccess(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::Branch(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::FunctionCall(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::Return(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::Precompile(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::Panic(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::DecomposeBits(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::CounterHint(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::Print(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::DynamicAlloc(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::StaticAlloc(instr) => instr.compile(ctx, remaining_lines),
            SimpleLine::LocationReport(instr) => instr.compile(ctx, remaining_lines),
        }
    }
}

impl Display for SimpleLine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SimpleLine::Match(instr) => write!(f, "{}", instr),
            SimpleLine::Assignment(instr) => write!(f, "{}", instr),
            SimpleLine::RawMemoryAccess(instr) => write!(f, "{}", instr),
            SimpleLine::Branch(instr) => write!(f, "{}", instr),
            SimpleLine::FunctionCall(instr) => write!(f, "{}", instr),
            SimpleLine::Return(instr) => write!(f, "{}", instr),
            SimpleLine::Precompile(instr) => write!(f, "{}", instr),
            SimpleLine::Panic(instr) => write!(f, "{}", instr),
            SimpleLine::DecomposeBits(instr) => write!(f, "{}", instr),
            SimpleLine::CounterHint(instr) => write!(f, "{}", instr),
            SimpleLine::Print(instr) => write!(f, "{}", instr),
            SimpleLine::DynamicAlloc(instr) => write!(f, "{}", instr),
            SimpleLine::StaticAlloc(instr) => write!(f, "{}", instr),
            SimpleLine::LocationReport(instr) => write!(f, "{}", instr),
        }
    }
}

impl IndentedDisplay for SimpleLine {
    fn to_string_with_indent(&self, indent: usize) -> String {
        match self {
            SimpleLine::Match(instr) => instr.to_string_with_indent(indent),
            SimpleLine::Assignment(instr) => instr.to_string_with_indent(indent),
            SimpleLine::RawMemoryAccess(instr) => instr.to_string_with_indent(indent),
            SimpleLine::Branch(instr) => instr.to_string_with_indent(indent),
            SimpleLine::FunctionCall(instr) => instr.to_string_with_indent(indent),
            SimpleLine::Return(instr) => instr.to_string_with_indent(indent),
            SimpleLine::Precompile(instr) => instr.to_string_with_indent(indent),
            SimpleLine::Panic(instr) => instr.to_string_with_indent(indent),
            SimpleLine::DecomposeBits(instr) => instr.to_string_with_indent(indent),
            SimpleLine::CounterHint(instr) => instr.to_string_with_indent(indent),
            SimpleLine::Print(instr) => instr.to_string_with_indent(indent),
            SimpleLine::DynamicAlloc(instr) => instr.to_string_with_indent(indent),
            SimpleLine::StaticAlloc(instr) => instr.to_string_with_indent(indent),
            SimpleLine::LocationReport(instr) => instr.to_string_with_indent(indent),
        }
    }
}

impl FindInternalVars for SimpleLine {
    fn find_internal_vars(&self) -> BTreeSet<Var> {
        match self {
            SimpleLine::Match(instr) => instr.find_internal_vars(),
            SimpleLine::Assignment(instr) => instr.find_internal_vars(),
            SimpleLine::RawMemoryAccess(instr) => instr.find_internal_vars(),
            SimpleLine::Branch(instr) => instr.find_internal_vars(),
            SimpleLine::FunctionCall(instr) => instr.find_internal_vars(),
            SimpleLine::Return(instr) => instr.find_internal_vars(),
            SimpleLine::Precompile(instr) => instr.find_internal_vars(),
            SimpleLine::Panic(instr) => instr.find_internal_vars(),
            SimpleLine::DecomposeBits(instr) => instr.find_internal_vars(),
            SimpleLine::CounterHint(instr) => instr.find_internal_vars(),
            SimpleLine::Print(instr) => instr.find_internal_vars(),
            SimpleLine::DynamicAlloc(instr) => instr.find_internal_vars(),
            SimpleLine::StaticAlloc(instr) => instr.find_internal_vars(),
            SimpleLine::LocationReport(instr) => instr.find_internal_vars(),
        }
    }
}

/// Compiles a sequence of SimpleLine instructions.
pub fn compile_lines(
    lines: &[SimpleLine],
    compiler: &mut Compiler,
    final_jump: Option<Label>,
    declared_vars: &mut BTreeSet<Var>,
) -> CompileResult {
    let mut instructions = Vec::new();
    let mut ctx = CompileContext::new(compiler, final_jump, declared_vars);

    for (i, line) in lines.iter().enumerate() {
        instructions.extend(line.compile(&mut ctx, &lines[i + 1..])?);
        // Some instructions (like control flow) handle remaining lines themselves
        if should_stop_processing(line) {
            return Ok(instructions);
        }
    }

    // Add final jump if specified
    if let Some(jump_label) = ctx.final_jump {
        instructions.push(IntermediateInstruction::Jump {
            dest: IntermediateValue::label(jump_label),
            updated_fp: None,
        });
    }

    Ok(instructions)
}

/// Determines if instruction processing should stop after this instruction.
const fn should_stop_processing(line: &SimpleLine) -> bool {
    matches!(
        line,
        SimpleLine::Match(_) | SimpleLine::Branch(_) | SimpleLine::FunctionCall(_)
    )
}

/// Finds all internal variables declared within a set of instructions.
pub fn find_internal_vars(lines: &[SimpleLine]) -> BTreeSet<Var> {
    lines
        .iter()
        .flat_map(FindInternalVars::find_internal_vars)
        .collect()
}
