use super::instruction::IntermediateInstruction;
use lean_vm::Label;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

/// Container for the complete intermediate representation of a program.
///
/// This structure holds all the compiled intermediate bytecode along with
/// metadata needed for execution and analysis.
#[derive(Debug, Clone)]
pub struct IntermediateBytecode {
    /// Main bytecode organized by function labels.
    ///
    /// Each label corresponds to a function entry point.
    pub bytecode: BTreeMap<Label, Vec<IntermediateInstruction>>,

    /// Match statement bytecode blocks.
    ///
    /// Each match statement produces multiple case blocks.
    pub match_blocks: Vec<Vec<Vec<IntermediateInstruction>>>,

    /// Memory requirements for each function.
    ///
    /// Maps function names to their stack frame size.
    pub memory_size_per_function: BTreeMap<String, usize>,
}

impl Display for IntermediateBytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (label, instructions) in &self.bytecode {
            writeln!(f, "\n{label}:")?;
            for instruction in instructions {
                writeln!(f, "  {instruction}")?;
            }
        }
        for (i, match_blocks) in self.match_blocks.iter().enumerate() {
            writeln!(f, "\nMatch {i}:")?;
            for (j, case) in match_blocks.iter().enumerate() {
                writeln!(f, "  Case {j}:")?;
                for instruction in case {
                    writeln!(f, "    {instruction}")?;
                }
            }
        }
        writeln!(f, "\nMemory size per function:")?;
        for (function_name, size) in &self.memory_size_per_function {
            writeln!(f, "{function_name}: {size}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{instruction::IntermediateInstruction, value::IntermediateValue};
    use crate::lang::ConstExpression;
    use lean_vm::Label;

    #[test]
    fn test_intermediate_bytecode_creation() {
        let bytecode = IntermediateBytecode {
            bytecode: BTreeMap::new(),
            match_blocks: Vec::new(),
            memory_size_per_function: BTreeMap::new(),
        };

        assert!(bytecode.bytecode.is_empty());
        assert!(bytecode.match_blocks.is_empty());
        assert!(bytecode.memory_size_per_function.is_empty());
    }

    #[test]
    fn test_intermediate_bytecode_with_functions() {
        let mut bytecode = IntermediateBytecode {
            bytecode: BTreeMap::new(),
            match_blocks: Vec::new(),
            memory_size_per_function: BTreeMap::new(),
        };

        let label1 = Label::function("main");
        let label2 = Label::function("helper");

        let instructions1 = vec![
            IntermediateInstruction::Computation {
                operation: lean_vm::Operation::Add,
                arg_a: IntermediateValue::MemoryAfterFp {
                    offset: ConstExpression::scalar(1),
                },
                arg_c: IntermediateValue::MemoryAfterFp {
                    offset: ConstExpression::scalar(2),
                },
                res: IntermediateValue::MemoryAfterFp {
                    offset: ConstExpression::scalar(3),
                },
            },
            IntermediateInstruction::Panic,
        ];

        let instructions2 = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(4),
            },
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(5),
            },
        }];

        bytecode.bytecode.insert(label1.clone(), instructions1);
        bytecode.bytecode.insert(label2.clone(), instructions2);

        bytecode
            .memory_size_per_function
            .insert("main".to_string(), 10);
        bytecode
            .memory_size_per_function
            .insert("helper".to_string(), 5);

        assert_eq!(bytecode.bytecode.len(), 2);
        assert_eq!(bytecode.memory_size_per_function.len(), 2);
        assert!(bytecode.bytecode.contains_key(&label1));
        assert!(bytecode.bytecode.contains_key(&label2));
        assert_eq!(bytecode.memory_size_per_function.get("main"), Some(&10));
        assert_eq!(bytecode.memory_size_per_function.get("helper"), Some(&5));
    }

    #[test]
    fn test_intermediate_bytecode_with_match_blocks() {
        let mut bytecode = IntermediateBytecode {
            bytecode: BTreeMap::new(),
            match_blocks: Vec::new(),
            memory_size_per_function: BTreeMap::new(),
        };

        let case1_instructions = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::Constant(ConstExpression::scalar(1)),
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(6),
            },
        }];

        let case2_instructions = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::Constant(ConstExpression::scalar(2)),
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(7),
            },
        }];

        let match_block1 = vec![case1_instructions, case2_instructions];

        let case3_instructions = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::Constant(ConstExpression::scalar(3)),
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(8),
            },
        }];

        let match_block2 = vec![case3_instructions];

        bytecode.match_blocks.push(match_block1);
        bytecode.match_blocks.push(match_block2);

        assert_eq!(bytecode.match_blocks.len(), 2);
        assert_eq!(bytecode.match_blocks[0].len(), 2); // Two cases in first match
        assert_eq!(bytecode.match_blocks[1].len(), 1); // One case in second match

        // Check first match block structure
        assert_eq!(bytecode.match_blocks[0][0].len(), 1); // One instruction in case 1
        assert_eq!(bytecode.match_blocks[0][1].len(), 1); // One instruction in case 2
        assert_eq!(bytecode.match_blocks[1][0].len(), 1); // One instruction in case 3
    }

    #[test]
    fn test_intermediate_bytecode_clone() {
        let mut original = IntermediateBytecode {
            bytecode: BTreeMap::new(),
            match_blocks: Vec::new(),
            memory_size_per_function: BTreeMap::new(),
        };

        let label = Label::function("test");
        let instructions = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::Constant(ConstExpression::scalar(42)),
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(9),
            },
        }];

        original.bytecode.insert(label.clone(), instructions);
        original
            .memory_size_per_function
            .insert("test".to_string(), 8);

        let cloned = original.clone();

        // Verify clone has same content
        assert_eq!(cloned.bytecode.len(), 1);
        assert_eq!(cloned.memory_size_per_function.len(), 1);
        assert!(cloned.bytecode.contains_key(&label));
        assert_eq!(cloned.memory_size_per_function.get("test"), Some(&8));

        // Verify independence - modify original
        original
            .memory_size_per_function
            .insert("new_function".to_string(), 16);
        assert_eq!(original.memory_size_per_function.len(), 2);
        assert_eq!(cloned.memory_size_per_function.len(), 1);
    }

    #[test]
    fn test_intermediate_bytecode_display_empty() {
        let bytecode = IntermediateBytecode {
            bytecode: BTreeMap::new(),
            match_blocks: Vec::new(),
            memory_size_per_function: BTreeMap::new(),
        };

        let display_output = format!("{}", bytecode);

        // Should contain the header for memory size
        assert!(display_output.contains("Memory size per function:"));

        // Should be minimal content for empty bytecode
        assert!(display_output.lines().count() <= 3);
    }

    #[test]
    fn test_intermediate_bytecode_display_with_content() {
        let mut bytecode = IntermediateBytecode {
            bytecode: BTreeMap::new(),
            match_blocks: Vec::new(),
            memory_size_per_function: BTreeMap::new(),
        };

        let label = Label::function("main");
        let instructions = vec![
            IntermediateInstruction::Computation {
                operation: lean_vm::Operation::Add,
                arg_a: IntermediateValue::Constant(ConstExpression::scalar(42)),
                arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
                res: IntermediateValue::MemoryAfterFp {
                    offset: ConstExpression::scalar(10),
                },
            },
            IntermediateInstruction::Panic,
        ];

        let match_case = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::Constant(ConstExpression::scalar(100)),
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(11),
            },
        }];
        let match_block = vec![match_case];

        bytecode.bytecode.insert(label, instructions);
        bytecode.match_blocks.push(match_block);
        bytecode
            .memory_size_per_function
            .insert("main".to_string(), 16);

        let display_output = format!("{}", bytecode);

        // Check function label appears
        assert!(display_output.contains("main:"));

        // Check instructions appear with proper indentation
        assert!(display_output.contains("m[fp + 10] = 42 + 0"));
        assert!(display_output.contains("  panic"));

        // Check match block appears
        assert!(display_output.contains("Match 0:"));
        assert!(display_output.contains("Case 0:"));
        assert!(display_output.contains("m[fp + 11] = 100 + 0"));

        // Check memory size appears
        assert!(display_output.contains("Memory size per function:"));
        assert!(display_output.contains("main: 16"));
    }

    #[test]
    fn test_intermediate_bytecode_display_multiple_match_blocks() {
        let mut bytecode = IntermediateBytecode {
            bytecode: BTreeMap::new(),
            match_blocks: Vec::new(),
            memory_size_per_function: BTreeMap::new(),
        };

        // First match block with 2 cases
        let case1 = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::Constant(ConstExpression::scalar(200)),
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(12),
            },
        }];
        let case2 = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::Constant(ConstExpression::scalar(300)),
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(13),
            },
        }];
        let match_block1 = vec![case1, case2];

        // Second match block with 1 case
        let case3 = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::Constant(ConstExpression::scalar(400)),
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(14),
            },
        }];
        let match_block2 = vec![case3];

        bytecode.match_blocks.push(match_block1);
        bytecode.match_blocks.push(match_block2);

        let display_output = format!("{}", bytecode);

        // Check both match blocks appear
        assert!(display_output.contains("Match 0:"));
        assert!(display_output.contains("Match 1:"));

        // Check cases in first match
        assert!(display_output.contains("Case 0:"));
        assert!(display_output.contains("Case 1:"));
        assert!(display_output.contains("m[fp + 12] = 200 + 0"));
        assert!(display_output.contains("m[fp + 13] = 300 + 0"));

        // Check case in second match
        assert!(display_output.contains("m[fp + 14] = 400 + 0"));
    }

    #[test]
    fn test_intermediate_bytecode_debug_format() {
        let mut bytecode = IntermediateBytecode {
            bytecode: BTreeMap::new(),
            match_blocks: Vec::new(),
            memory_size_per_function: BTreeMap::new(),
        };

        let label = Label::function("test");
        let instructions = vec![IntermediateInstruction::Computation {
            operation: lean_vm::Operation::Add,
            arg_a: IntermediateValue::Constant(ConstExpression::scalar(500)),
            arg_c: IntermediateValue::Constant(ConstExpression::scalar(0)),
            res: IntermediateValue::MemoryAfterFp {
                offset: ConstExpression::scalar(15),
            },
        }];

        bytecode.bytecode.insert(label, instructions);
        bytecode
            .memory_size_per_function
            .insert("test".to_string(), 4);

        let debug_output = format!("{:?}", bytecode);

        // Debug format should contain struct name and fields
        assert!(debug_output.contains("IntermediateBytecode"));
        assert!(debug_output.contains("bytecode:"));
        assert!(debug_output.contains("match_blocks:"));
        assert!(debug_output.contains("memory_size_per_function:"));

        // Should contain the actual data
        assert!(debug_output.contains("test"));
        assert!(debug_output.contains("500"));
        assert!(debug_output.contains("15"));
    }
}
