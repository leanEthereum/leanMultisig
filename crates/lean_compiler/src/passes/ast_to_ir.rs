//! AST to IR conversion pass.
//!
//! This pass converts the high-level AST representation to the simplified
//! intermediate representation (IR) used by the backend.
//!
//! This is the final transformation pass that produces the clean IR
//! ready for code generation.

use super::{Pass, PassResult};
use crate::ir::{ArrayManager, ConstMalloc, Counters, SimpleFunction, SimpleProgram, conversion};
use crate::lang::Program;
use std::collections::BTreeMap;

/// Pass for converting AST to simplified IR
///
/// This pass performs the final transformation from the high-level AST
/// to the simplified IR that the backend can easily consume.
pub struct AstToIrPass {
    /// The resulting IR program after conversion
    pub result: Option<SimpleProgram>,
}

impl AstToIrPass {
    /// Create a new AST-to-IR conversion pass
    pub fn new() -> Self {
        Self { result: None }
    }

    /// Get the converted IR program after running the pass
    ///
    /// This consumes the result, so it can only be called once.
    pub fn take_result(&mut self) -> Option<SimpleProgram> {
        self.result.take()
    }

    /// Convert a single AST program to IR
    ///
    /// This is the core conversion logic, kept simple and focused.
    fn convert_program(&self, program: &Program) -> SimpleProgram {
        let mut ir_functions = BTreeMap::new();
        let mut counters = Counters::default();
        let mut const_malloc = ConstMalloc::default();

        // Convert each function from AST to IR
        for (name, ast_function) in &program.functions {
            let mut array_manager = ArrayManager::default();

            // Convert the function body to simplified IR instructions
            let ir_instructions = conversion::simplify_lines(
                &ast_function.body,
                &mut counters,
                &mut ir_functions,
                false, // is_function_param
                &mut array_manager,
                &mut const_malloc,
            );

            // Extract non-const arguments (const args should have been processed by ConstEvalPass)
            let ir_arguments = ast_function
                .arguments
                .iter()
                .map(|(var_name, is_const)| {
                    if *is_const {
                        panic!("Constant arguments should have been processed by ConstEvalPass before AST-to-IR conversion");
                    }
                    var_name.clone()
                })
                .collect();

            // Create the IR function
            let ir_function = SimpleFunction {
                name: name.clone(),
                arguments: ir_arguments,
                n_returned_vars: ast_function.n_returned_vars,
                instructions: ir_instructions,
            };

            ir_functions.insert(name.clone(), ir_function);

            // Clear const_malloc state for next function
            const_malloc.map.clear();
        }

        SimpleProgram {
            functions: ir_functions,
        }
    }
}

impl Default for AstToIrPass {
    fn default() -> Self {
        Self::new()
    }
}

impl Pass for AstToIrPass {
    fn name(&self) -> &'static str {
        "ast_to_ir"
    }

    fn run(&mut self, program: &mut Program) -> PassResult {
        // Convert the AST program to IR
        let ir_program = self.convert_program(program);
        self.result = Some(ir_program);
        Ok(())
    }

    fn requires(&self) -> &[&'static str] {
        // Must run after all AST transformations are complete
        &["inline", "const_eval", "ssa_repair"]
    }

    fn invalidates(&self) -> &[&'static str] {
        // This is typically the final pass, so it doesn't invalidate anything
        &[]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::Function;
    use std::collections::BTreeMap;

    #[test]
    fn test_ast_to_ir_conversion() {
        let mut program = Program {
            functions: BTreeMap::new(),
        };

        // Create a simple function for testing
        let function = Function {
            name: "test_func".to_string(),
            arguments: vec![("x".to_string(), false)],
            inlined: false,
            body: vec![], // Empty body for simplicity
            n_returned_vars: 1,
        };
        program.functions.insert("test_func".to_string(), function);

        let mut pass = AstToIrPass::new();
        let result = pass.run(&mut program);

        assert!(result.is_ok());
        assert!(pass.result.is_some());

        let ir_program = pass.take_result().unwrap();
        assert_eq!(ir_program.functions.len(), 1);
        assert!(ir_program.functions.contains_key("test_func"));

        let ir_function = &ir_program.functions["test_func"];
        assert_eq!(ir_function.name, "test_func");
        assert_eq!(ir_function.arguments, vec!["x".to_string()]);
        assert_eq!(ir_function.n_returned_vars, 1);
    }

    #[test]
    fn test_const_argument_validation() {
        let mut program = Program {
            functions: BTreeMap::new(),
        };

        // Create a function with const arguments (should panic)
        let function = Function {
            name: "const_func".to_string(),
            arguments: vec![("x".to_string(), false), ("const_arg".to_string(), true)],
            inlined: false,
            body: vec![],
            n_returned_vars: 1,
        };
        program.functions.insert("const_func".to_string(), function);

        let mut pass = AstToIrPass::new();

        // Should panic because const arguments weren't processed
        let result =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| pass.run(&mut program)));

        assert!(
            result.is_err(),
            "Should panic on unprocessed const arguments"
        );
    }
}
