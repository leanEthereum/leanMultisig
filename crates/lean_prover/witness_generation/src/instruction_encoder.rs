use lean_vm::*;
use multilinear_toolkit::prelude::*;

pub fn field_representation(instr: &Instruction) -> [F; N_INSTRUCTION_COLUMNS] {
    let mut fields = [F::ZERO; N_INSTRUCTION_COLUMNS];
    match instr {
        Instruction::Computation {
            operation,
            arg_a,
            arg_c,
            res,
        } => {
            match operation {
                Operation::Add => {
                    fields[instr_idx(COL_INDEX_ADD)] = F::ONE;
                }
                Operation::Mul => {
                    fields[instr_idx(COL_INDEX_MUL)] = F::ONE;
                }
            }

            set_nu_a(&mut fields, arg_a);
            set_nu_b(&mut fields, res);
            set_nu_c(&mut fields, arg_c);
        }
        Instruction::Deref { shift_0, shift_1, res } => {
            fields[instr_idx(COL_INDEX_DEREF)] = F::ONE;
            fields[instr_idx(COL_INDEX_FLAG_A)] = F::ZERO;
            fields[instr_idx(COL_INDEX_OPERAND_A)] = F::from_usize(*shift_0);
            fields[instr_idx(COL_INDEX_FLAG_C)] = F::ONE;
            fields[instr_idx(COL_INDEX_OPERAND_C)] = F::from_usize(*shift_1);
            match res {
                MemOrFpOrConstant::Constant(cst) => {
                    fields[instr_idx(COL_INDEX_AUX_1)] = F::ONE;
                    fields[instr_idx(COL_INDEX_FLAG_B)] = F::ONE;
                    fields[instr_idx(COL_INDEX_OPERAND_B)] = *cst;
                }
                MemOrFpOrConstant::MemoryAfterFp { offset } => {
                    fields[instr_idx(COL_INDEX_AUX_1)] = F::ONE;
                    fields[instr_idx(COL_INDEX_FLAG_B)] = F::ZERO;
                    fields[instr_idx(COL_INDEX_OPERAND_B)] = F::from_usize(*offset);
                }
                MemOrFpOrConstant::Fp => {
                    fields[instr_idx(COL_INDEX_AUX_1)] = F::ZERO;
                    fields[instr_idx(COL_INDEX_FLAG_B)] = F::ONE;
                }
            }
        }
        Instruction::Jump {
            condition,
            label: _,
            dest,
            updated_fp,
        } => {
            fields[instr_idx(COL_INDEX_JUMP)] = F::ONE;
            set_nu_a(&mut fields, condition);
            set_nu_b(&mut fields, dest);
            set_nu_c(&mut fields, updated_fp);
        }
        Instruction::Precompile {
            table,
            arg_a,
            arg_b,
            arg_c,
            aux_1,
            aux_2,
        } => {
            fields[instr_idx(COL_INDEX_IS_PRECOMPILE)] = F::ONE;
            fields[instr_idx(COL_INDEX_WHICH_PRECOMPILE)] = table.embed();
            set_nu_a(&mut fields, arg_a);
            set_nu_b(&mut fields, arg_b);
            set_nu_c(&mut fields, arg_c);
            fields[instr_idx(COL_INDEX_AUX_1)] = F::from_usize(*aux_1);
            fields[instr_idx(COL_INDEX_AUX_2)] = F::from_usize(*aux_2);
        }
    }
    fields
}

fn set_nu_a(fields: &mut [F; N_INSTRUCTION_COLUMNS], a: &MemOrConstant) {
    match a {
        MemOrConstant::Constant(cst) => {
            fields[instr_idx(COL_INDEX_FLAG_A)] = F::ONE;
            fields[instr_idx(COL_INDEX_OPERAND_A)] = *cst;
        }
        MemOrConstant::MemoryAfterFp { offset } => {
            fields[instr_idx(COL_INDEX_FLAG_A)] = F::ZERO;
            fields[instr_idx(COL_INDEX_OPERAND_A)] = F::from_usize(*offset);
        }
    }
}

fn set_nu_b(fields: &mut [F; N_INSTRUCTION_COLUMNS], b: &MemOrConstant) {
    match b {
        MemOrConstant::Constant(cst) => {
            fields[instr_idx(COL_INDEX_FLAG_B)] = F::ONE;
            fields[instr_idx(COL_INDEX_OPERAND_B)] = *cst;
        }
        MemOrConstant::MemoryAfterFp { offset } => {
            fields[instr_idx(COL_INDEX_FLAG_B)] = F::ZERO;
            fields[instr_idx(COL_INDEX_OPERAND_B)] = F::from_usize(*offset);
        }
    }
}

fn set_nu_c(fields: &mut [F; N_INSTRUCTION_COLUMNS], c: &MemOrFp) {
    match c {
        MemOrFp::Fp => {
            fields[instr_idx(COL_INDEX_FLAG_C)] = F::ONE;
        }
        MemOrFp::MemoryAfterFp { offset } => {
            fields[instr_idx(COL_INDEX_FLAG_C)] = F::ZERO;
            fields[instr_idx(COL_INDEX_OPERAND_C)] = F::from_usize(*offset);
        }
    }
}
