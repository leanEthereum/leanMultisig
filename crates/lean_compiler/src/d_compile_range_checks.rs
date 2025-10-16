use lean_vm::*;
use p3_field::PrimeCharacteristicRing;
use std::collections::{BTreeMap, BTreeSet};
use utils::ToUsize;

#[derive(Debug, Clone)]
pub struct RangeCheckInfo {
    pub hint_fp: usize,
    pub v_pos: usize,
    pub v: usize,
    pub t: usize,
    pub q: usize, // t - 1 - v
}

fn find_next_zero_cell(memory: &Memory, start_offset: usize) -> Option<usize> {
    if start_offset >= memory.0.len() {
        return None;
    }
    let mut z = start_offset;

    loop {
        if z >= memory.0.len() {
            break;
        }
        let m_fp_z = &memory.get(z);
        if !m_fp_z.is_err() && m_fp_z.clone().unwrap() == F::ZERO {
            return Some(z);
        }
        z += 1;
    }
    None
}

fn find_next_undefined_cell_from_mem(
    mem: &Memory,
    conflicts: &BTreeSet<usize>,
    pos: usize,
) -> usize {
    let mut z = pos;

    while !matches!(mem.get(z), Err(RunnerError::UndefinedMemory)) {
        z += 1;
    }

    loop {
        if conflicts.contains(&z) {
            z = find_next_undefined_cell_from_mem(mem, conflicts, z + 1);
        } else {
            break;
        }
    }
    z
}

pub fn is_undef(mem: &Memory, pos: usize) -> bool {
    matches!(mem.get(pos), Err(RunnerError::UndefinedMemory))
}

pub fn compile_range_checks(
    first_exec: &ExecutionResult,
    bytecode: &Bytecode,
) -> Result<Bytecode, RunnerError> {
    // Early return if no range checks exist
    if !bytecode
        .hints
        .values()
        .any(|hints| hints.iter().any(|h| matches!(h, Hint::RangeCheck { .. })))
    {
        return Ok(bytecode.clone());
    }

    // Convenience mapping: instr_idx -> RangeCheckInfo
    let mut rcs: BTreeMap<(usize, usize), RangeCheckInfo> = BTreeMap::new();

    // Validate that the last fp is 0
    let last_fp = first_exec.fps.last().ok_or(RunnerError::PCOutOfBounds)?; // Using existing error type
    if *last_fp != 0 {
        return Err(RunnerError::PCOutOfBounds); // Using existing error type for now
    }

    // Find the penultimate instruction
    let pen_instr = bytecode.instructions[first_exec.pcs[first_exec.pcs.len() - 2]].clone();

    // Assume that the penultimate instruction is a JUMP
    assert!(matches!(pen_instr, Instruction::Jump { .. }));

    // Assume that the destination of the penultimate jump is the last instruction
    match pen_instr {
        Instruction::Jump { dest, .. } => match dest {
            MemOrConstant::Constant(c) => {
                assert_eq!(c.to_usize(), first_exec.pcs[first_exec.pcs.len() - 1]);
            }
            MemOrConstant::MemoryAfterFp { .. } => {
                unreachable!();
            }
        },
        _ => {}
    }

    // Keep track of memory locations we will write to
    let mut conflicts: BTreeSet<usize> = BTreeSet::new();

    for (pc, hints) in &bytecode.hints {
        for (hint_idx, hint) in hints.iter().enumerate() {
            match hint {
                Hint::RangeCheck { value, max } => {
                    let v_off = match value {
                        MemOrFp::MemoryAfterFp { offset } => *offset,
                        MemOrFp::Fp => 0, // fp is at offset 0
                    };
                    let execution_step = first_exec.pcs.iter().position(|&p| p == *pc).unwrap();
                    let hint_fp = first_exec.fps[execution_step];
                    let v_pos = hint_fp + v_off;
                    let v = first_exec.memory.get(v_pos).unwrap().to_usize();
                    let t = match max {
                        MemOrConstant::MemoryAfterFp { .. } => {
                            unreachable!();
                        }
                        MemOrConstant::Constant(c) => c.to_usize(),
                    };

                    // q = t - 1 - v in the field
                    let q = (F::from_usize(t) - F::ONE - F::from_usize(v)).to_usize();

                    rcs.insert(
                        (*pc, hint_idx),
                        RangeCheckInfo {
                            hint_fp,
                            v_pos,
                            v,
                            t,
                            q,
                        },
                    );

                    conflicts.insert(v);
                    conflicts.insert(t);
                }
                _ => {}
            }
        }
    }

    // Since the range check vals are referenced by offset, our fp must be the smallest possible
    // value: 0.
    let fp = 0;

    let mut instrs_to_insert: Vec<Instruction> = vec![];

    // Look for any 0 cells past fp, or create one
    let z_pos = find_next_zero_cell(&first_exec.memory, fp).unwrap_or_else(|| {
        let z_pos = find_next_undefined_cell_from_mem(&first_exec.memory, &conflicts, fp);
        if first_exec.memory.get(z_pos).is_err() {
            let z_instr = Instruction::Computation {
                operation: Operation::Add,
                arg_a: MemOrConstant::Constant(F::ZERO),
                arg_c: MemOrFp::MemoryAfterFp { offset: z_pos - fp },
                res: MemOrConstant::Constant(F::ZERO),
            };
            instrs_to_insert.push(z_instr);
        }
        z_pos
    });

    conflicts.insert(z_pos);

    for ((_pc, _hint_idx), rc_info) in &rcs {
        // Step 1: DEREF m[m[fp + x]] == m[fp + i]
        let i = if is_undef(&first_exec.memory, rc_info.v) {
            // if m[v] is undefined, use z
            z_pos
        } else {
            // if m[v] is defined, then search for an i where m[fp + i] is undefined
            find_next_undefined_cell_from_mem(&first_exec.memory, &conflicts, fp)
        };
        let step_1 = Instruction::Deref {
            shift_0: rc_info.v_pos - fp,
            shift_1: 0,
            res: MemOrFpOrConstant::MemoryAfterFp { offset: i - fp },
        };

        // Since the step 1 deref writes to m[i], add i to conflicts
        conflicts.insert(i);

        // Step 2: ADD m[fp + j] = t - 1 - v
        let j = find_next_undefined_cell_from_mem(&first_exec.memory, &conflicts, i);
        let step_2 = Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::ZERO), // 0
            arg_c: MemOrFp::MemoryAfterFp { offset: j - fp }, // Unknown; solves to t - 1 - v
            res: MemOrConstant::Constant(F::from_usize(rc_info.q)), // t - 1 - v
        };

        // Since the step 2 add writes to m[j], add j to conflicts
        conflicts.insert(j);

        // Step 3: DEREF m[fp + k] = m[m[fp + j]]
        let k = if is_undef(&first_exec.memory, rc_info.q) && !conflicts.contains(&rc_info.q) {
            // if m[q] is undefined, use z
            z_pos
        } else {
            // if m[q] is defined, then search for an k where m[fp + k] is undefined
            find_next_undefined_cell_from_mem(&first_exec.memory, &conflicts, j)
        };

        let step_3 = Instruction::Deref {
            shift_0: j - fp,
            shift_1: 0,
            res: MemOrFpOrConstant::MemoryAfterFp { offset: k - fp },
        };

        // Since the step 3 deref may write to m[k] or m[q], add q and k to conflicts
        conflicts.insert(k);
        conflicts.insert(rc_info.q);

        instrs_to_insert.push(step_1);
        instrs_to_insert.push(step_2);
        instrs_to_insert.push(step_3);
    }

    // Create the updated bytecode with range check instructions appended at the end
    let mut updated_bytecode = bytecode.clone();

    // Find the index of the penultimate instruction in the instruction list
    let penultimate_pc = first_exec.pcs[first_exec.pcs.len() - 2];

    // Append the range check instructions to the end
    let first_range_check_pc = updated_bytecode.instructions.len();
    updated_bytecode.instructions.extend(instrs_to_insert);

    // Add a final jump that terminates execution
    updated_bytecode.instructions.push(Instruction::Jump {
        condition: MemOrConstant::Constant(F::ZERO), // Never jump - terminates execution
        dest: MemOrConstant::Constant(F::ZERO),      // Doesn't matter since condition is false
        updated_fp: MemOrFp::Fp,
        label: Label::custom("termination_jump".to_string()),
    });

    // Update the penultimate jump to point to the first range check instruction
    if let Instruction::Jump { dest, .. } = &mut updated_bytecode.instructions[penultimate_pc] {
        *dest = MemOrConstant::Constant(F::from_usize(first_range_check_pc));
    }

    // Update ending_pc to point after the final jump
    updated_bytecode.ending_pc = updated_bytecode.instructions.len();

    Ok(updated_bytecode)
}
