use lean_vm::*;
use p3_field::PrimeCharacteristicRing;

use crate::*;

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
                    fields[6] = F::ONE;
                }
                Operation::Mul => {
                    fields[7] = F::ONE;
                }
            }

            set_nu_a(&mut fields, arg_a);
            set_nu_b(&mut fields, res);
            set_nu_c(&mut fields, arg_c);
        }
        Instruction::Deref {
            shift_0,
            shift_1,
            res,
        } => {
            fields[3] = F::ZERO; // flag_A = 0
            fields[0] = F::from_usize(*shift_0);
            fields[5] = F::ONE; // flag_C = 1
            fields[2] = F::from_usize(*shift_1);
            match res {
                MemOrFpOrConstant::Constant(cst) => {
                    fields[10] = F::ONE; // AUX = 1
                    fields[4] = F::ONE; // flag_B = 1
                    fields[1] = *cst;
                }
                MemOrFpOrConstant::MemoryAfterFp { offset } => {
                    fields[10] = F::ONE; // AUX = 1
                    fields[4] = F::ZERO; // flag_B = 0
                    fields[1] = F::from_usize(*offset);
                }
                MemOrFpOrConstant::Fp => {
                    fields[10] = F::ZERO; // AUX = 0
                    fields[4] = F::ONE; // flag_B = 1
                }
            }
        }
        Instruction::Jump {
            condition,
            label: _,
            dest,
            updated_fp,
        } => {
            fields[9] = F::ONE; // JUMP = 1
            set_nu_a(&mut fields, condition);
            set_nu_b(&mut fields, dest);
            set_nu_c(&mut fields, updated_fp);
        }
        Instruction::Poseidon2_16 { arg_a, arg_b, res } => {
            fields[11] = F::ONE; // POSEIDON_16 = 1
            set_nu_a(&mut fields, arg_a);
            set_nu_b(&mut fields, arg_b);
            set_nu_c(&mut fields, res);
        }
        Instruction::Poseidon2_24 { arg_a, arg_b, res } => {
            fields[12] = F::ONE; // POSEIDON_24 = 1
            set_nu_a(&mut fields, arg_a);
            set_nu_b(&mut fields, arg_b);
            set_nu_c(&mut fields, res);
        }
        Instruction::DotProductExtensionExtension {
            arg0,
            arg1,
            res,
            size,
        } => {
            fields[13] = F::ONE; // DOT_PRODUCT_EXTENSION = 1
            set_nu_a(&mut fields, arg0);
            set_nu_b(&mut fields, arg1);
            set_nu_c(&mut fields, res);
            fields[10] = F::from_usize(*size); // AUX stores size
        }
        Instruction::MultilinearEval {
            coeffs,
            point,
            res,
            n_vars,
        } => {
            fields[COL_INDEX_MULTILINEAR_EVAL] = F::ONE;
            set_nu_a(&mut fields, coeffs);
            set_nu_b(&mut fields, point);
            set_nu_c(&mut fields, res);
            fields[COL_INDEX_AUX] = F::from_usize(*n_vars); // AUX stores `n_vars`
        }
    }
    fields
}

fn set_nu_a(fields: &mut [F; N_INSTRUCTION_COLUMNS], a: &MemOrConstant) {
    match a {
        MemOrConstant::Constant(cst) => {
            fields[COL_INDEX_FLAG_A] = F::ONE;
            fields[COL_INDEX_OPERAND_A] = *cst;
        }
        MemOrConstant::MemoryAfterFp { offset } => {
            fields[COL_INDEX_FLAG_A] = F::ZERO;
            fields[COL_INDEX_OPERAND_A] = F::from_usize(*offset);
        }
    }
}

fn set_nu_b(fields: &mut [F; N_INSTRUCTION_COLUMNS], b: &MemOrConstant) {
    match b {
        MemOrConstant::Constant(cst) => {
            fields[COL_INDEX_FLAG_B] = F::ONE;
            fields[COL_INDEX_OPERAND_B] = *cst;
        }
        MemOrConstant::MemoryAfterFp { offset } => {
            fields[COL_INDEX_FLAG_B] = F::ZERO;
            fields[COL_INDEX_OPERAND_B] = F::from_usize(*offset);
        }
    }
}

fn set_nu_c(fields: &mut [F; N_INSTRUCTION_COLUMNS], c: &MemOrFp) {
    match c {
        MemOrFp::Fp => {
            fields[COL_INDEX_FLAG_C] = F::ONE;
        }
        MemOrFp::MemoryAfterFp { offset } => {
            fields[COL_INDEX_FLAG_C] = F::ZERO;
            fields[COL_INDEX_OPERAND_C] = F::from_usize(*offset);
        }
    }
}
