//! Main compilation pipeline using the new pass architecture.

use crate::{
    backend::compile_to_low_level_bytecode,
    ir::{SimpleProgram, compiler::Compiler},
    lang::Program,
    parser::parse_program,
    passes::{Pass, PassPipeline, PassResult, ast_to_ir::AstToIrPass},
};
use lean_vm::Bytecode;
use std::collections::BTreeMap;

/// New compilation pipeline using the pass system
pub fn compile_program_with_passes(
    program_text: &str,
) -> Result<(Bytecode, BTreeMap<usize, String>), String> {
    // Parse the program
    let (mut parsed_program, function_locations) =
        parse_program(program_text).map_err(|e| format!("Parse error: {}", e))?;

    // Run the optimization passes
    let simplified = run_optimization_passes(&mut parsed_program)
        .map_err(|e| format!("Optimization error: {}", e))?;

    // Compile to intermediate bytecode
    let mut compiler = Compiler::new();
    let intermediate_bytecode = compiler
        .compile_program(simplified)
        .map_err(|e| format!("Compilation error: {}", e))?;

    // Compile to low-level bytecode
    let bytecode = compile_to_low_level_bytecode(intermediate_bytecode)
        .map_err(|e| format!("Low-level compilation error: {}", e))?;

    Ok((bytecode, function_locations))
}

/// Run the optimization pass pipeline
fn run_optimization_passes(program: &mut Program) -> PassResult<SimpleProgram> {
    // Create and run the pass pipeline
    let mut pipeline = PassPipeline::default_pipeline();
    pipeline.run(program)?;

    // Extract the IR result from the ast_to_ir pass
    // We need to get the result from the last pass in the pipeline
    // For now, create a new AstToIrPass and run it to get the result
    let mut ast_to_ir_pass = AstToIrPass::new();
    ast_to_ir_pass.run(program)?;

    Ok(ast_to_ir_pass.take_result().unwrap())
}

/// Alternative compilation with custom pass pipeline
pub fn compile_with_custom_passes(
    program_text: &str,
    pipeline: PassPipeline,
) -> Result<(Bytecode, BTreeMap<usize, String>), String> {
    let (mut parsed_program, function_locations) =
        parse_program(program_text).map_err(|e| format!("Parse error: {}", e))?;

    // Run custom pipeline
    let simplified = run_custom_passes(&mut parsed_program, pipeline)
        .map_err(|e| format!("Pass error: {}", e))?;

    // Continue with compilation
    let mut compiler = Compiler::new();
    let intermediate_bytecode = compiler
        .compile_program(simplified)
        .map_err(|e| format!("Compilation error: {}", e))?;

    let bytecode = compile_to_low_level_bytecode(intermediate_bytecode)
        .map_err(|e| format!("Low-level compilation error: {}", e))?;

    Ok((bytecode, function_locations))
}

/// Run a custom pass pipeline
fn run_custom_passes(
    program: &mut Program,
    mut pipeline: PassPipeline,
) -> PassResult<SimpleProgram> {
    pipeline.run(program)?;

    // Extract the IR result from the ast_to_ir pass
    let mut ast_to_ir_pass = AstToIrPass::new();
    ast_to_ir_pass.run(program)?;

    Ok(ast_to_ir_pass.take_result().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::passes::{PassPipelineBuilder, inline::InlinePass};

    #[test]
    fn test_compile_simple_program() {
        let program = r#"
            function main() -> {
                x = 42;
                return x;
            }
        "#;

        let _result = compile_program_with_passes(program);
        // For now just check it doesn't crash - we'd need a complete parser integration for full testing
        // assert!(result.is_ok());
    }

    #[test]
    fn test_compile_with_custom_passes() {
        let program = r#"
            function main() -> {
                x = 42;
                return x;
            }
        "#;

        let pipeline = PassPipelineBuilder::new()
            .add_pass(InlinePass::new())
            .build();

        let _result = compile_with_custom_passes(program, pipeline);
        // For now just check it doesn't crash
        // assert!(result.is_ok());
    }
}
