//! Human-readable pretty-printer for the final lean ISA bytecode.
//!
//! Output is grouped by high-level function: each user-defined or specialized
//! function appears as a top-level block (with its argument names and stack
//! offsets), followed by its body. Loop-derived sub-functions are nested
//! inside the body of the function they were lifted from. Inlined functions
//! are not shown — they were duplicated into every call site at compile time.
//!
//! The lean compiler emits each function as several distinct labelled blocks
//! (the entry, plus continuations after each call, plus if/else branches,
//! etc.), interleaved in pc order. We reconstruct each function's full body
//! by attributing every non-function label-block to a function block via the
//! bytecode's constant references (jumps and stored continuation pcs).
//!
//! Padding instructions appended to round bytecode size up to a power of two
//! are stripped from the output.
//!
//! Entry point: [`Bytecode::pretty_print`].
use std::collections::{BTreeMap, BTreeSet};

use backend::PrimeField32;

use crate::core::Label;
use crate::isa::{Bytecode, CodeEntry};
use crate::{CodeAddress, Hint, Instruction, MemOrConstant, MemOrFpOrConstant};

/// Pretty-print the bytecode grouped by high-level function.
pub fn pretty_print_bytecode(bytecode: &Bytecode) -> String {
    Printer::new(bytecode).render()
}

impl Bytecode {
    /// Render this bytecode in a human-readable form (see module docs).
    pub fn pretty_print(&self) -> String {
        pretty_print_bytecode(self)
    }
}

/// One contiguous labelled region of the bytecode.
#[derive(Debug, Clone)]
struct Section {
    start_pc: CodeAddress,
    end_pc: CodeAddress, // exclusive
    label: Label,
}

struct Printer<'a> {
    bytecode: &'a Bytecode,
    /// All sections (one per Label hint), sorted by start_pc.
    sections: Vec<Section>,
    /// section index -> classified kind.
    kinds: Vec<SectionKind>,
    /// Indices of sections that are function entries (one of `FunctionEntry*`).
    function_indices: Vec<usize>,
    /// For each section, the function-entry section it belongs to. Function
    /// entries belong to themselves.
    owner: Vec<usize>,
    /// For each function entry index, the parent function entry in the display
    /// tree (loop-derived entries only). `None` means top-level.
    parent: Vec<Option<usize>>,
    /// For each function entry, the list of nested-loop child entries.
    children: Vec<Vec<usize>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SectionKind {
    UserDefined,
    Specialized,
    Loop,
    ParallelLoop,
    EndProgram,
    /// Continuation after a call, an if/else branch, etc. — not a real entry.
    NonEntry,
}

impl SectionKind {
    fn is_function_entry(self) -> bool {
        !matches!(self, Self::NonEntry)
    }
    fn is_loop(self) -> bool {
        matches!(self, Self::Loop | Self::ParallelLoop)
    }
    fn header(self) -> &'static str {
        match self {
            Self::UserDefined => "fn",
            Self::Specialized => "fn[specialized]",
            Self::Loop => "loop",
            Self::ParallelLoop => "parallel_loop",
            Self::EndProgram => "fn[end_program]",
            Self::NonEntry => "",
        }
    }
}

impl<'a> Printer<'a> {
    fn new(bytecode: &'a Bytecode) -> Self {
        let real_len = effective_len(bytecode);
        let sections = collect_sections(bytecode, real_len);
        let kinds = sections.iter().map(|s| classify(&s.label)).collect::<Vec<_>>();

        let mut function_indices: Vec<usize> = (0..sections.len()).filter(|i| kinds[*i].is_function_entry()).collect();
        function_indices.sort_by_key(|&i| sections[i].start_pc);

        // Map section start_pc -> section index, for fast lookup.
        let pc_to_section: BTreeMap<CodeAddress, usize> =
            sections.iter().enumerate().map(|(i, s)| (s.start_pc, i)).collect();

        // Build a reverse index: for each constant reference inside the
        // bytecode, record the section that produced it.
        let mut references: BTreeMap<CodeAddress, BTreeSet<usize>> = BTreeMap::new();
        for (sec_idx, sec) in sections.iter().enumerate() {
            for pc in sec.start_pc..sec.end_pc {
                for target in instruction_constant_targets(&bytecode.code[pc].instruction) {
                    if pc_to_section.contains_key(&target) {
                        references.entry(target).or_default().insert(sec_idx);
                    }
                }
            }
        }

        // Function-entry sections own themselves. Each non-entry section
        // belongs to whichever function entry transitively references its
        // start_pc. Propagate ownership iteratively until fixed point so
        // chains like (function -> return_from_call -> if_else_end) resolve
        // correctly.
        let mut owner: Vec<Option<usize>> = vec![None; sections.len()];
        for (i, kind) in kinds.iter().enumerate() {
            if kind.is_function_entry() {
                owner[i] = Some(i);
            }
        }
        loop {
            let mut changed = false;
            for i in 0..sections.len() {
                if owner[i].is_some() {
                    continue;
                }
                if let Some(refs) = references.get(&sections[i].start_pc) {
                    // Pick the closest already-resolved owner (in pc terms).
                    let mut best: Option<(usize, usize)> = None; // (distance, owner)
                    for &ref_sec in refs {
                        if let Some(o) = owner[ref_sec] {
                            let d =
                                (sections[ref_sec].start_pc as isize - sections[i].start_pc as isize).unsigned_abs();
                            if best.map(|(bd, _)| d < bd).unwrap_or(true) {
                                best = Some((d, o));
                            }
                        }
                    }
                    if let Some((_, o)) = best {
                        owner[i] = Some(o);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        // Anything still unresolved: fall back to source-location, then to
        // the previous function entry in pc order.
        for i in 0..sections.len() {
            if owner[i].is_some() {
                continue;
            }
            owner[i] = owner_by_source_location(i, &sections, &kinds, bytecode).or_else(|| {
                function_indices
                    .iter()
                    .rev()
                    .copied()
                    .find(|&fi| sections[fi].start_pc <= sections[i].start_pc)
            });
        }
        let owner: Vec<usize> = owner.into_iter().enumerate().map(|(i, o)| o.unwrap_or(i)).collect();

        // For loop-function nesting: a loop is "parented" by the function
        // entry whose body sets up the call to the loop. The setup of a call
        // writes the new frame's saved-pc and saved-fp into a new memory
        // region, then issues a Jump whose `dest` is the loop's start_pc.
        // We detect this by walking each function's owned sections and
        // looking for jumps to other function-entry start_pcs.
        let mut callers_of: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        for sec_idx in 0..sections.len() {
            let owning = owner[sec_idx];
            for pc in sections[sec_idx].start_pc..sections[sec_idx].end_pc {
                if let Instruction::Jump {
                    dest: MemOrConstant::Constant(dest),
                    ..
                } = &bytecode.code[pc].instruction
                {
                    let dest_pc = dest.as_canonical_u32() as usize;
                    if let Some(&callee_section) = pc_to_section.get(&dest_pc)
                        && kinds[callee_section].is_function_entry()
                        && callee_section != owning
                    {
                        callers_of.entry(callee_section).or_default().insert(owning);
                    }
                }
            }
        }

        // Walk caller chain to find a non-loop ancestor for each loop entry.
        let mut parent = vec![None; sections.len()];
        for &loop_idx in &function_indices {
            if !kinds[loop_idx].is_loop() {
                continue;
            }
            let mut current = loop_idx;
            let mut visited = BTreeSet::from([loop_idx]);
            while let Some(callers) = callers_of.get(&current) {
                let next = callers
                    .iter()
                    .copied()
                    .find(|c| !visited.contains(c) && kinds[*c].is_function_entry());
                match next {
                    None => break,
                    Some(caller) => {
                        if !kinds[caller].is_loop() {
                            parent[loop_idx] = Some(caller);
                            break;
                        }
                        visited.insert(caller);
                        current = caller;
                    }
                }
            }
        }

        let mut children: Vec<Vec<usize>> = vec![Vec::new(); sections.len()];
        for &loop_idx in &function_indices {
            if let Some(p) = parent[loop_idx] {
                children[p].push(loop_idx);
            }
        }
        for cs in &mut children {
            cs.sort_by_key(|&c| sections[c].start_pc);
        }

        Self {
            bytecode,
            sections,
            kinds,
            function_indices,
            owner,
            parent,
            children,
        }
    }

    fn render(&self) -> String {
        let mut out = String::new();
        let mut top_level: Vec<usize> = self
            .function_indices
            .iter()
            .copied()
            .filter(|&i| self.parent[i].is_none())
            .collect();
        top_level.sort_by_key(|&i| self.sections[i].start_pc);

        for (i, fn_idx) in top_level.iter().enumerate() {
            if i > 0 {
                out.push('\n');
            }
            self.render_function(*fn_idx, 0, &mut out);
        }
        out
    }

    fn render_function(&self, fn_idx: usize, depth: usize, out: &mut String) {
        let section = &self.sections[fn_idx];
        let kind = self.kinds[fn_idx];
        let indent = "  ".repeat(depth);
        let body_indent = "  ".repeat(depth + 1);
        let inner_indent = "  ".repeat(depth + 2);

        let display_name = match &section.label {
            Label::Function(name) => name.clone(),
            other => other.to_string(),
        };
        out.push_str(&format!("{indent}{} {display_name} {{\n", kind.header()));

        // Argument list.
        if let Label::Function(name) = &section.label
            && let Some(args) = self.bytecode.function_arguments.get(name)
        {
            if args.is_empty() {
                out.push_str(&format!("{body_indent}args: ()\n"));
            } else {
                let pretty = args
                    .iter()
                    .enumerate()
                    .map(|(i, name)| format!("m[fp + {}] = {}", i + 2, name))
                    .collect::<Vec<_>>()
                    .join(", ");
                out.push_str(&format!("{body_indent}args: [{pretty}]\n"));
            }
        }

        // Collect all sections owned by this function entry, sorted by pc.
        let mut owned: Vec<usize> = self
            .owner
            .iter()
            .enumerate()
            .filter(|&(_, &o)| o == fn_idx)
            .map(|(i, _)| i)
            .collect();
        owned.sort_by_key(|&i| self.sections[i].start_pc);

        out.push_str(&format!("{body_indent}body:\n"));

        // Children (nested loops) get spliced in at the position of their
        // start_pc relative to the owned sections.
        let child_starts: BTreeMap<CodeAddress, usize> = self.children[fn_idx]
            .iter()
            .map(|&c| (self.sections[c].start_pc, c))
            .collect();

        for sec_idx in owned {
            let sec = &self.sections[sec_idx];
            // Sub-section header (so the user sees boundaries between e.g.
            // the function entry, its return-from-call continuations and
            // its if/else branches).
            if sec_idx != fn_idx {
                out.push_str(&format!("{body_indent}; section {}:\n", sec.label));
            }
            for pc in sec.start_pc..sec.end_pc {
                if let Some(&child_idx) = child_starts.get(&pc) {
                    self.render_function(child_idx, depth + 2, out);
                }
                self.render_pc(pc, &inner_indent, out);
            }
        }

        // Loop children whose start_pc is past every owned section: render at end.
        let owned_ends: BTreeSet<CodeAddress> = self
            .owner
            .iter()
            .enumerate()
            .filter(|&(_, &o)| o == fn_idx)
            .map(|(i, _)| self.sections[i].start_pc)
            .collect();
        for &child in &self.children[fn_idx] {
            if !owned_ends.contains(&self.sections[child].start_pc) {
                // We may have already rendered it inside the loop above
                // (because its start_pc fell inside an owned section). Skip
                // if so.
                let already_rendered = self
                    .owner
                    .iter()
                    .enumerate()
                    .filter(|&(_, &o)| o == fn_idx)
                    .any(|(i, _)| {
                        let s = &self.sections[i];
                        (s.start_pc..s.end_pc).contains(&self.sections[child].start_pc)
                    });
                if !already_rendered {
                    self.render_function(child, depth + 1, out);
                }
            }
        }

        out.push_str(&format!("{indent}}}\n"));
    }

    fn render_pc(&self, pc: CodeAddress, indent: &str, out: &mut String) {
        let entry: &CodeEntry = &self.bytecode.code[pc];
        for hint in entry.hints.iter() {
            if matches!(hint, Hint::LocationReport { .. } | Hint::Label { .. }) {
                continue;
            }
            out.push_str(&format!("{indent}; hint: {hint}\n"));
        }
        out.push_str(&format!("{indent}{pc:>5}: {}\n", entry.instruction));
    }
}

/// Strip the trailing padding instructions added to round the program length
/// up to a power of two: the compiler fills the tail with copies of the last
/// real instruction, so we walk back while the entry equals its predecessor.
fn effective_len(bytecode: &Bytecode) -> CodeAddress {
    let total = bytecode.code.len();
    if total < 2 {
        return total;
    }
    let mut end = total;
    while end > 1 && bytecode.code[end - 1] == bytecode.code[end - 2] {
        end -= 1;
    }
    end
}

/// Collect every `Hint::Label` and turn it into a section. Sections are
/// disjoint and cover the range `[0, real_len)`.
fn collect_sections(bytecode: &Bytecode, real_len: CodeAddress) -> Vec<Section> {
    let mut starts: Vec<(CodeAddress, Label)> = Vec::new();
    for (pc, entry) in bytecode.code.iter().enumerate().take(real_len) {
        for hint in entry.hints.iter() {
            if let Hint::Label { label } = hint {
                starts.push((pc, label.clone()));
            }
        }
    }
    starts.sort_by_key(|(pc, _)| *pc);
    // De-dup multiple labels at the same pc, keep the one that's a Function
    // if any; otherwise keep the first.
    let mut deduped: Vec<(CodeAddress, Label)> = Vec::new();
    for (pc, label) in starts {
        if let Some(last) = deduped.last_mut()
            && last.0 == pc
        {
            if matches!(last.1, Label::Function(_)) {
                continue;
            }
            if matches!(label, Label::Function(_)) {
                *last = (pc, label);
            }
            continue;
        }
        deduped.push((pc, label));
    }

    let mut out = Vec::with_capacity(deduped.len());
    for i in 0..deduped.len() {
        let (start_pc, label) = deduped[i].clone();
        let end_pc = deduped.get(i + 1).map(|(p, _)| *p).unwrap_or(real_len);
        out.push(Section {
            start_pc,
            end_pc,
            label,
        });
    }
    out
}

fn classify(label: &Label) -> SectionKind {
    match label {
        Label::Function(name) => {
            if name.starts_with("@parallel_loop_") {
                SectionKind::ParallelLoop
            } else if name.starts_with("@loop_") {
                SectionKind::Loop
            } else if is_specialized_name(name) {
                SectionKind::Specialized
            } else {
                SectionKind::UserDefined
            }
        }
        Label::EndProgram => SectionKind::EndProgram,
        _ => SectionKind::NonEntry,
    }
}

/// Specialized const-arg variants are emitted as `original_arg=val_arg=val`.
/// User function names can't contain `=` (it isn't a valid identifier char),
/// so the presence of `=` is a reliable marker.
fn is_specialized_name(name: &str) -> bool {
    !name.starts_with('@') && name.contains('=')
}

/// All constant pc-targets referenced by an instruction's operands.
fn instruction_constant_targets(instr: &Instruction) -> Vec<CodeAddress> {
    let mut out = Vec::new();
    let push_mc = |c: &MemOrConstant, out: &mut Vec<CodeAddress>| {
        if let MemOrConstant::Constant(c) = c {
            out.push(c.as_canonical_u32() as usize);
        }
    };
    let push_mfc = |c: &MemOrFpOrConstant, out: &mut Vec<CodeAddress>| {
        if let MemOrFpOrConstant::Constant(c) = c {
            out.push(c.as_canonical_u32() as usize);
        }
    };
    match instr {
        Instruction::Computation { arg_a, arg_c, res, .. } => {
            push_mc(arg_a, &mut out);
            push_mfc(arg_c, &mut out);
            push_mc(res, &mut out);
        }
        Instruction::Deref { res, .. } => {
            push_mfc(res, &mut out);
        }
        Instruction::Jump {
            condition,
            dest,
            updated_fp,
            ..
        } => {
            push_mc(condition, &mut out);
            push_mc(dest, &mut out);
            push_mfc(updated_fp, &mut out);
        }
        Instruction::Precompile(_) => {}
    }
    out
}

fn owner_by_source_location(
    sec_idx: usize,
    sections: &[Section],
    kinds: &[SectionKind],
    bytecode: &Bytecode,
) -> Option<usize> {
    let pc = sections[sec_idx].start_pc;
    let loc = bytecode.pc_to_location.get(pc)?;
    let func_name = bytecode
        .function_locations
        .range(..=*loc)
        .next_back()
        .map(|(_, n)| n.clone())?;
    sections
        .iter()
        .enumerate()
        .find_map(|(i, s)| match (&s.label, kinds[i]) {
            (Label::Function(n), SectionKind::UserDefined) if *n == func_name => Some(i),
            _ => None,
        })
}
