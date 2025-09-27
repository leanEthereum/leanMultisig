use crate::{F, ONE_VEC_PTR, PUBLIC_INPUT_START, ZERO_VEC_PTR, lang::*};
use lean_vm::{CodeAddress, Label};
use p3_field::PrimeCharacteristicRing;
use std::collections::BTreeMap;
use utils::ToUsize;

/// Low-level bytecode generator state for constant evaluation.
#[derive(Debug)]
pub struct CodeGenerator {
    /// Memory size allocated per function.
    pub memory_size_per_function: BTreeMap<String, usize>,
    /// Mapping from labels to program counter addresses.
    pub label_to_pc: BTreeMap<Label, CodeAddress>,
    /// Size of each match statement block.
    pub match_block_sizes: Vec<usize>,
    /// Starting address of first block for each match statement.
    pub match_first_block_starts: Vec<CodeAddress>,
}

/// Evaluates a constant value to a concrete usize.
pub fn eval_constant_value(constant: &ConstantValue, compiler: &CodeGenerator) -> usize {
    match constant {
        ConstantValue::Scalar(scalar) => *scalar,
        ConstantValue::PublicInputStart => PUBLIC_INPUT_START,
        ConstantValue::PointerToZeroVector => ZERO_VEC_PTR,
        ConstantValue::PointerToOneVector => ONE_VEC_PTR,
        ConstantValue::FunctionSize { function_name } => {
            let func_name_str = match function_name {
                Label::Function(name) => name,
                _ => panic!("Expected function label, got: {function_name}"),
            };
            *compiler
                .memory_size_per_function
                .get(func_name_str)
                .unwrap_or_else(|| panic!("Function {func_name_str} not found in memory size map"))
        }
        ConstantValue::Label(label) => compiler.label_to_pc.get(label).copied().unwrap(),
        ConstantValue::MatchBlockSize { match_index } => compiler.match_block_sizes[*match_index],
        ConstantValue::MatchFirstBlockStart { match_index } => {
            compiler.match_first_block_starts[*match_index]
        }
    }
}

/// Evaluates a constant expression to a field element.
pub fn eval_const_expression(constant: &ConstExpression, compiler: &CodeGenerator) -> F {
    constant
        .eval_with(&|cst| Some(F::from_usize(eval_constant_value(cst, compiler))))
        .unwrap()
}

/// Evaluates a constant expression to a usize.
pub fn eval_const_expression_usize(constant: &ConstExpression, compiler: &CodeGenerator) -> usize {
    eval_const_expression(constant, compiler).to_usize()
}

/// Tries to evaluate an intermediate value as a constant field element.
pub fn try_as_constant(
    value: &crate::ir::IntermediateValue,
    compiler: &CodeGenerator,
) -> Option<F> {
    if let crate::ir::IntermediateValue::Constant(c) = value {
        Some(eval_const_expression(c, compiler))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::{ConstExpression, ConstantValue};
    use lean_vm::Label;
    use std::collections::BTreeMap;

    #[test]
    fn test_eval_constant_value_scalar() {
        let compiler = CodeGenerator {
            memory_size_per_function: BTreeMap::new(),
            label_to_pc: BTreeMap::new(),
            match_block_sizes: Vec::new(),
            match_first_block_starts: Vec::new(),
        };

        let constant = ConstantValue::Scalar(42);
        assert_eq!(eval_constant_value(&constant, &compiler), 42);
    }

    #[test]
    fn test_eval_constant_value_public_input_start() {
        let compiler = CodeGenerator {
            memory_size_per_function: BTreeMap::new(),
            label_to_pc: BTreeMap::new(),
            match_block_sizes: Vec::new(),
            match_first_block_starts: Vec::new(),
        };

        let constant = ConstantValue::PublicInputStart;
        assert_eq!(
            eval_constant_value(&constant, &compiler),
            PUBLIC_INPUT_START
        );
    }

    #[test]
    fn test_eval_constant_value_function_size() {
        let mut compiler = CodeGenerator {
            memory_size_per_function: BTreeMap::new(),
            label_to_pc: BTreeMap::new(),
            match_block_sizes: Vec::new(),
            match_first_block_starts: Vec::new(),
        };
        compiler
            .memory_size_per_function
            .insert("test_function".to_string(), 100);

        let constant = ConstantValue::FunctionSize {
            function_name: Label::function("test_function"),
        };
        assert_eq!(eval_constant_value(&constant, &compiler), 100);
    }

    #[test]
    fn test_eval_constant_value_label() {
        let mut compiler = CodeGenerator {
            memory_size_per_function: BTreeMap::new(),
            label_to_pc: BTreeMap::new(),
            match_block_sizes: Vec::new(),
            match_first_block_starts: Vec::new(),
        };
        let label = Label::function("test_label");
        compiler.label_to_pc.insert(label.clone(), 50);

        let constant = ConstantValue::Label(label);
        assert_eq!(eval_constant_value(&constant, &compiler), 50);
    }

    #[test]
    fn test_eval_constant_value_match_block_size() {
        let compiler = CodeGenerator {
            memory_size_per_function: BTreeMap::new(),
            label_to_pc: BTreeMap::new(),
            match_block_sizes: vec![10, 20, 30],
            match_first_block_starts: Vec::new(),
        };

        let constant = ConstantValue::MatchBlockSize { match_index: 1 };
        assert_eq!(eval_constant_value(&constant, &compiler), 20);
    }

    #[test]
    fn test_eval_const_expression_scalar() {
        let compiler = CodeGenerator {
            memory_size_per_function: BTreeMap::new(),
            label_to_pc: BTreeMap::new(),
            match_block_sizes: Vec::new(),
            match_first_block_starts: Vec::new(),
        };

        let expression = ConstExpression::scalar(42);
        let result = eval_const_expression(&expression, &compiler);
        assert_eq!(result.to_usize(), 42);
    }

    #[test]
    fn test_eval_const_expression_usize() {
        let compiler = CodeGenerator {
            memory_size_per_function: BTreeMap::new(),
            label_to_pc: BTreeMap::new(),
            match_block_sizes: Vec::new(),
            match_first_block_starts: Vec::new(),
        };

        let expression = ConstExpression::scalar(42);
        assert_eq!(eval_const_expression_usize(&expression, &compiler), 42);
    }

    #[test]
    fn test_try_as_constant_success() {
        use crate::ir::IntermediateValue;

        let compiler = CodeGenerator {
            memory_size_per_function: BTreeMap::new(),
            label_to_pc: BTreeMap::new(),
            match_block_sizes: Vec::new(),
            match_first_block_starts: Vec::new(),
        };

        let value = IntermediateValue::Constant(ConstExpression::scalar(42));
        let result = try_as_constant(&value, &compiler);
        assert!(result.is_some());
        assert_eq!(result.unwrap().to_usize(), 42);
    }

    #[test]
    fn test_try_as_constant_failure() {
        use crate::ir::IntermediateValue;

        let compiler = CodeGenerator {
            memory_size_per_function: BTreeMap::new(),
            label_to_pc: BTreeMap::new(),
            match_block_sizes: Vec::new(),
            match_first_block_starts: Vec::new(),
        };

        let value = IntermediateValue::Fp;
        let result = try_as_constant(&value, &compiler);
        assert!(result.is_none());
    }
}
