use backend::*;
use lean_vm::*;

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
                    fields[instr_idx(COL_AUX)] = F::ONE; // ADD = P_1(AUX=1) = 1
                }
                Operation::Mul => {
                    fields[instr_idx(COL_MUL)] = F::ONE;
                }
            }

            set_nu_a(&mut fields, arg_a);
            set_nu_b(&mut fields, res);
            set_nu_c(&mut fields, arg_c);
        }
        Instruction::Deref { shift_0, shift_1, res } => {
            // AUX=2: DEREF = P_2(AUX=2) = 1
            fields[instr_idx(COL_AUX)] = F::TWO;
            // value_A = m[fp + shift_0]
            fields[instr_idx(COL_FLAG_A)] = F::ZERO;
            fields[instr_idx(COL_OPERAND_A)] = F::from_usize(*shift_0);
            // addr_B = value_A + operand_B, flag_B=1 so standard addr_b constraint is vacuous
            fields[instr_idx(COL_FLAG_B)] = F::ONE;
            fields[instr_idx(COL_OPERAND_B)] = F::from_usize(*shift_1);
            // encodes the result via nu_C
            set_nu_c(&mut fields, res);
        }
        Instruction::Jump {
            condition,
            label: _,
            dest,
            updated_fp,
        } => {
            fields[instr_idx(COL_JUMP)] = F::ONE;
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
            let precompile_data = match *table {
                Table::Poseidon16(_) => POSEIDON_PRECOMPILE_DATA,
                Table::ExtensionOp(_) => {
                    assert!(*aux_2 == 0 || *aux_2 == 1);
                    let is_be = *aux_2;
                    let op_flag = match *aux_1 {
                        0 => 4,  // ADD: flag_add = 1
                        1 => 8,  // MUL: flag_mul = 1
                        2 => 16, // POLY_EQ: flag_poly_eq = 1
                        _ => unreachable!("invalid extension_op op_type"),
                    };
                    2 * is_be + op_flag
                }
                _ => unreachable!("unknown precompile table"),
            };
            fields[instr_idx(COL_PRECOMPILE_DATA)] = F::from_usize(precompile_data);
            match (arg_a, arg_b) {
                (MemOrFpOrConstant::FpRelative { offset: off_a }, MemOrFpOrConstant::FpRelative { offset: off_b }) => {
                    fields[instr_idx(COL_FLAG_AB_FP)] = F::ONE;
                    fields[instr_idx(COL_OPERAND_A)] = F::from_usize(*off_a);
                    fields[instr_idx(COL_OPERAND_B)] = F::from_usize(*off_b);
                }
                (a, b) => {
                    set_nu_a(&mut fields, &a.as_mem_or_constant());
                    set_nu_b(&mut fields, &b.as_mem_or_constant());
                }
            }
            set_nu_c(&mut fields, arg_c);
        }
    }
    fields
}

fn set_nu_a(fields: &mut [F; N_INSTRUCTION_COLUMNS], a: &MemOrConstant) {
    match a {
        MemOrConstant::Constant(cst) => {
            fields[instr_idx(COL_FLAG_A)] = F::ONE;
            fields[instr_idx(COL_OPERAND_A)] = *cst;
        }
        MemOrConstant::MemoryAfterFp { offset } => {
            fields[instr_idx(COL_FLAG_A)] = F::ZERO;
            fields[instr_idx(COL_OPERAND_A)] = F::from_usize(*offset);
        }
    }
}

fn set_nu_b(fields: &mut [F; N_INSTRUCTION_COLUMNS], b: &MemOrConstant) {
    match b {
        MemOrConstant::Constant(cst) => {
            fields[instr_idx(COL_FLAG_B)] = F::ONE;
            fields[instr_idx(COL_OPERAND_B)] = *cst;
        }
        MemOrConstant::MemoryAfterFp { offset } => {
            fields[instr_idx(COL_FLAG_B)] = F::ZERO;
            fields[instr_idx(COL_OPERAND_B)] = F::from_usize(*offset);
        }
    }
}

#[inline(always)]
fn set_nu_c(fields: &mut [F; N_INSTRUCTION_COLUMNS], c: &MemOrFpOrConstant) {
    match c {
        MemOrFpOrConstant::FpRelative { offset } => {
            fields[instr_idx(COL_FLAG_C_FP)] = F::ONE;
            fields[instr_idx(COL_OPERAND_C)] = F::from_usize(*offset);
        }
        MemOrFpOrConstant::MemoryAfterFp { offset } => {
            fields[instr_idx(COL_FLAG_C)] = F::ZERO;
            fields[instr_idx(COL_OPERAND_C)] = F::from_usize(*offset);
        }
        MemOrFpOrConstant::Constant(cst) => {
            fields[instr_idx(COL_FLAG_C)] = F::ONE;
            fields[instr_idx(COL_OPERAND_C)] = *cst;
        }
    }
}
