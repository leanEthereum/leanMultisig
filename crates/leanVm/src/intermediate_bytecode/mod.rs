use std::{collections::BTreeMap, fmt};

use crate::{
    bytecode::{
        Bytecode,
        hint::Hint,
        instruction::{
            Instruction, computation::ComputationInstruction, deref::DerefInstruction,
            dot_product::DotProductInstruction, jump::JumpIfNotZeroInstruction,
            multilinear_eval::MultilinearEvalInstruction, poseidon16::Poseidon2_16Instruction,
            poseidon24::Poseidon2_24Instruction,
        },
        operand::{MemOrConstant, MemOrFp, MemOrFpOrConstant},
        operation::Operation,
    },
    compiler::Compiler,
    lang::{Label, const_expr::ConstExpression},
};

pub mod intermediate_value;
pub use intermediate_value::*;
pub mod operation;
pub use operation::*;
pub mod instruction;
pub use instruction::*;

#[derive(Debug, Clone)]
pub struct IntermediateBytecode {
    pub bytecode: BTreeMap<Label, Vec<IntermediateInstruction>>,
    pub memory_size_per_function: BTreeMap<String, usize>,
}

impl IntermediateBytecode {
    #[allow(clippy::too_many_lines)]
    pub fn to_bytecode(mut self) -> Result<Bytecode, String> {
        self.bytecode.insert(
            "@end_program".to_string(),
            vec![IntermediateInstruction::Jump {
                dest: IntermediateValue::label("@end_program".to_string()),
                updated_fp: None,
            }],
        );

        let starting_frame_memory = *self.memory_size_per_function.get("main").unwrap();

        let mut label_to_pc = BTreeMap::new();
        label_to_pc.insert("@function_main".to_string(), 0);
        let entrypoint = self
            .bytecode
            .remove("@function_main")
            .ok_or("No main function found in the compiled program")?;

        let mut code_chunks = vec![(0, entrypoint.clone())];
        let mut pc = entrypoint.iter().filter(|i| !i.is_hint()).count();
        for (label, instructions) in &self.bytecode {
            label_to_pc.insert(label.clone(), pc);
            code_chunks.push((pc, instructions.clone()));
            pc += instructions.iter().filter(|i| !i.is_hint()).count();
        }

        let ending_pc = label_to_pc.get("@end_program").copied().unwrap();

        let mut low_level_bytecode = Vec::new();
        let mut hints = BTreeMap::new();

        let compiler = Compiler {
            memory_size_per_function: self.memory_size_per_function,
            label_to_pc,
        };

        let try_as_mem_or_constant = |value: &IntermediateValue| {
            if let Some(cst) = value.try_as_constant(&compiler) {
                return Some(MemOrConstant::Constant(cst));
            }
            if let IntermediateValue::MemoryAfterFp { offset } = value {
                return Some(MemOrConstant::MemoryAfterFp {
                    offset: offset.eval_usize(&compiler),
                });
            }
            None
        };

        let try_as_mem_or_fp = |value: &IntermediateValue| match value {
            IntermediateValue::MemoryAfterFp { offset } => Some(MemOrFp::MemoryAfterFp {
                offset: offset.eval_usize(&compiler),
            }),
            IntermediateValue::Fp => Some(MemOrFp::Fp),
            IntermediateValue::Constant(_) => None,
        };

        for (pc_start, chunk) in code_chunks {
            let mut pc = pc_start;
            for instruction in chunk {
                match instruction.clone() {
                    IntermediateInstruction::Computation {
                        operation,
                        mut arg_a,
                        mut arg_c,
                        res,
                    } => {
                        if let Some(arg_a_cst) = arg_a.try_as_constant(&compiler) {
                            if let Some(arg_b_cst) = arg_c.try_as_constant(&compiler) {
                                // res = constant +/x constant

                                let op_res = operation.compute(arg_a_cst, arg_b_cst);

                                let res: MemOrFp = res.try_into_mem_or_fp(&compiler).unwrap();

                                low_level_bytecode.push(Instruction::Computation(
                                    ComputationInstruction {
                                        operation: Operation::Add,
                                        arg_a: MemOrConstant::zero(),
                                        arg_c: res,
                                        res: MemOrConstant::Constant(op_res),
                                    },
                                ));
                                pc += 1;
                                continue;
                            }
                        }

                        if arg_c.is_constant() {
                            std::mem::swap(&mut arg_a, &mut arg_c);
                        }

                        low_level_bytecode.push(Instruction::Computation(ComputationInstruction {
                            operation,
                            arg_a: try_as_mem_or_constant(&arg_a).unwrap(),
                            arg_c: try_as_mem_or_fp(&arg_c).unwrap(),
                            res: try_as_mem_or_constant(&res).unwrap(),
                        }));
                    }
                    IntermediateInstruction::Panic => {
                        low_level_bytecode.push(Instruction::Computation(ComputationInstruction {
                            // fp x 0 = 1 is impossible, so we can use it to panic
                            operation: Operation::Mul,
                            arg_a: MemOrConstant::zero(),
                            arg_c: MemOrFp::Fp,
                            res: MemOrConstant::one(),
                        }));
                    }
                    IntermediateInstruction::Deref {
                        shift_0,
                        shift_1,
                        res,
                    } => {
                        low_level_bytecode.push(Instruction::Deref(DerefInstruction {
                            shift_0: shift_0.eval_usize(&compiler),
                            shift_1: shift_1.eval_usize(&compiler),
                            res: match res {
                                IntermediaryMemOrFpOrConstant::MemoryAfterFp { offset } => {
                                    MemOrFpOrConstant::MemoryAfterFp {
                                        offset: offset.eval_usize(&compiler),
                                    }
                                }
                                IntermediaryMemOrFpOrConstant::Fp => MemOrFpOrConstant::Fp,
                                IntermediaryMemOrFpOrConstant::Constant(c) => {
                                    MemOrFpOrConstant::Constant(c.eval(&compiler))
                                }
                            },
                        }));
                    }
                    IntermediateInstruction::JumpIfNotZero {
                        condition,
                        dest,
                        updated_fp,
                    } => {
                        let updated_fp =
                            updated_fp.map_or(MemOrFp::Fp, |fp| try_as_mem_or_fp(&fp).unwrap());
                        low_level_bytecode.push(Instruction::JumpIfNotZero(
                            JumpIfNotZeroInstruction {
                                condition: try_as_mem_or_constant(&condition).unwrap(),
                                dest: try_as_mem_or_constant(&dest).unwrap(),
                                updated_fp,
                            },
                        ));
                    }
                    IntermediateInstruction::Jump { dest, updated_fp } => {
                        low_level_bytecode.push(Instruction::JumpIfNotZero(
                            JumpIfNotZeroInstruction {
                                condition: MemOrConstant::one(),
                                dest: try_as_mem_or_constant(&dest).unwrap(),
                                updated_fp: updated_fp
                                    .map_or(MemOrFp::Fp, |fp| try_as_mem_or_fp(&fp).unwrap()),
                            },
                        ));
                    }
                    IntermediateInstruction::Poseidon2_16 { arg_a, arg_b, res } => {
                        low_level_bytecode.push(Instruction::Poseidon2_16(
                            Poseidon2_16Instruction {
                                arg_a: try_as_mem_or_constant(&arg_a).unwrap(),
                                arg_b: try_as_mem_or_constant(&arg_b).unwrap(),
                                res: try_as_mem_or_fp(&res).unwrap(),
                            },
                        ));
                    }
                    IntermediateInstruction::Poseidon2_24 { arg_a, arg_b, res } => {
                        low_level_bytecode.push(Instruction::Poseidon2_24(
                            Poseidon2_24Instruction {
                                arg_a: try_as_mem_or_constant(&arg_a).unwrap(),
                                arg_b: try_as_mem_or_constant(&arg_b).unwrap(),
                                res: try_as_mem_or_fp(&res).unwrap(),
                            },
                        ));
                    }
                    IntermediateInstruction::DotProduct {
                        arg0,
                        arg1,
                        res,
                        size,
                    } => {
                        low_level_bytecode.push(Instruction::DotProduct(DotProductInstruction {
                            arg0: arg0.try_into_mem_or_constant(&compiler).unwrap(),
                            arg1: arg1.try_into_mem_or_constant(&compiler).unwrap(),
                            res: res.try_into_mem_or_fp(&compiler).unwrap(),
                            size: size.eval_usize(&compiler),
                        }));
                    }
                    IntermediateInstruction::MultilinearEval {
                        coeffs,
                        point,
                        res,
                        n_vars,
                    } => {
                        low_level_bytecode.push(Instruction::MultilinearEval(
                            MultilinearEvalInstruction {
                                coeffs: coeffs.try_into_mem_or_constant(&compiler).unwrap(),
                                point: point.try_into_mem_or_constant(&compiler).unwrap(),
                                res: res.try_into_mem_or_fp(&compiler).unwrap(),
                                n_vars: n_vars.eval_usize(&compiler),
                            },
                        ));
                    }
                    IntermediateInstruction::DecomposeBits {
                        res_offset,
                        to_decompose,
                    } => {
                        let hint = Hint::DecomposeBits {
                            res_offset,
                            to_decompose: try_as_mem_or_constant(&to_decompose).unwrap(),
                        };
                        hints.entry(pc).or_insert_with(Vec::new).push(hint);
                    }
                    IntermediateInstruction::Inverse { arg, res_offset } => {
                        let hint = Hint::Inverse {
                            arg: try_as_mem_or_constant(&arg).unwrap(),
                            res_offset,
                        };
                        hints.entry(pc).or_insert_with(Vec::new).push(hint);
                    }
                    IntermediateInstruction::RequestMemory {
                        offset,
                        size,
                        vectorized,
                    } => {
                        let size = try_as_mem_or_constant(&size).unwrap();
                        let hint = Hint::RequestMemory {
                            offset: offset.eval_usize(&compiler),
                            vectorized,
                            size,
                        };
                        hints.entry(pc).or_insert_with(Vec::new).push(hint);
                    }
                    IntermediateInstruction::Print { line_info, content } => {
                        let hint = Hint::Print {
                            line_info: line_info.clone(),
                            content: content
                                .into_iter()
                                .map(|c| try_as_mem_or_constant(&c).unwrap())
                                .collect(),
                        };
                        hints.entry(pc).or_insert_with(Vec::new).push(hint);
                    }
                }

                if !instruction.is_hint() {
                    pc += 1;
                }
            }
        }

        Ok(Bytecode {
            instructions: low_level_bytecode,
            hints,
            starting_frame_memory,
            ending_pc,
        })
    }
}

impl fmt::Display for IntermediateBytecode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Iterate through each labeled block of instructions in the bytecode.
        for (label, instructions) in &self.bytecode {
            // Write the label for the current block, followed by a newline.
            writeln!(f, "\n{label}:")?;
            // Iterate through each instruction within the block.
            for instruction in instructions {
                // Write the instruction, indented with two spaces for readability.
                writeln!(f, "  {instruction}")?;
            }
        }

        // Write the header for the memory size section.
        writeln!(f, "\nMemory size per function:")?;
        // Iterate through the recorded memory sizes for each function.
        for (function_name, size) in &self.memory_size_per_function {
            // Write the function name and its corresponding memory size.
            writeln!(f, "{function_name}: {size}")?;
        }

        // Return Ok to indicate that formatting was successful.
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntermediaryMemOrFpOrConstant {
    MemoryAfterFp { offset: ConstExpression }, // m[fp + offset]
    Fp,
    Constant(ConstExpression),
}

impl fmt::Display for IntermediaryMemOrFpOrConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {offset}]"),
            Self::Fp => write!(f, "fp"),
            Self::Constant(c) => write!(f, "{c}"),
        }
    }
}
