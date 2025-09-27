//! Compiler transformation passes.

use crate::lang::Program;
use std::fmt;

pub mod ast_to_ir;
pub mod const_eval;
pub mod inline;
pub mod ssa_repair;

/// Error type for pass execution
#[derive(Debug, Clone, PartialEq)]
pub enum PassError {
    /// Pass failed with a specific message
    Failed(String),
    /// Pass hit an internal assertion
    InternalError(String),
    /// Pass exceeded maximum iterations or time limit
    Timeout(String),
}

impl fmt::Display for PassError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PassError::Failed(msg) => write!(f, "Pass failed: {}", msg),
            PassError::InternalError(msg) => write!(f, "Internal error: {}", msg),
            PassError::Timeout(msg) => write!(f, "Pass timeout: {}", msg),
        }
    }
}

impl std::error::Error for PassError {}

/// Result type for pass operations
pub type PassResult<T = ()> = Result<T, PassError>;

/// Trait for compiler transformation passes
pub trait Pass {
    /// Run this pass on the given program
    fn run(&mut self, program: &mut Program) -> PassResult;

    /// Get the name of this pass for debugging/logging
    fn name(&self) -> &'static str;

    /// Check if this pass has any preconditions
    fn requires(&self) -> &[&'static str] {
        &[]
    }

    /// Check if this pass invalidates other analysis results
    fn invalidates(&self) -> &[&'static str] {
        &[]
    }

    /// Check if this pass should be run (allows conditional passes)
    fn should_run(&self, _program: &Program) -> bool {
        true
    }
}

/// A configurable pipeline of compiler passes
#[allow(missing_debug_implementations)]
pub struct PassPipeline {
    passes: Vec<Box<dyn Pass>>,
    debug: bool,
}

impl PassPipeline {
    /// Create a new empty pass pipeline
    pub fn new() -> Self {
        Self {
            passes: Vec::new(),
            debug: false,
        }
    }

    /// Create the default pass pipeline for the lean compiler
    pub fn default_pipeline() -> Self {
        Self::new()
            .add_pass(inline::InlinePass::new())
            .add_pass(const_eval::ConstEvalPass::new())
            .add_pass(ssa_repair::SSARepairPass::new())
            .add_pass(ast_to_ir::AstToIrPass::new())
    }

    /// Add a pass to the pipeline
    pub fn add_pass<P: Pass + 'static>(mut self, pass: P) -> Self {
        self.passes.push(Box::new(pass));
        self
    }

    /// Enable debug output for the pipeline
    pub fn with_debug(mut self, debug: bool) -> Self {
        self.debug = debug;
        self
    }

    /// Run all passes in the pipeline on the given program
    pub fn run(&mut self, program: &mut Program) -> PassResult {
        for pass in &mut self.passes {
            if pass.should_run(program) {
                if self.debug {
                    eprintln!("Running pass: {}", pass.name());
                }

                pass.run(program).map_err(|e| {
                    PassError::Failed(format!("Pass '{}' failed: {}", pass.name(), e))
                })?;
            } else if self.debug {
                eprintln!("Skipping pass: {}", pass.name());
            }
        }
        Ok(())
    }

    /// Get the names of all passes in the pipeline
    pub fn pass_names(&self) -> Vec<&'static str> {
        self.passes.iter().map(|p| p.name()).collect()
    }

    /// Clear all passes from the pipeline
    pub fn clear(mut self) -> Self {
        self.passes.clear();
        self
    }
}

impl Default for PassPipeline {
    fn default() -> Self {
        Self::default_pipeline()
    }
}

/// Builder for constructing pass pipelines fluently
#[allow(missing_debug_implementations)]
pub struct PassPipelineBuilder {
    pipeline: PassPipeline,
}

impl PassPipelineBuilder {
    pub fn new() -> Self {
        Self {
            pipeline: PassPipeline::new(),
        }
    }

    pub fn add_pass<P: Pass + 'static>(mut self, pass: P) -> Self {
        self.pipeline = self.pipeline.add_pass(pass);
        self
    }

    pub fn debug(mut self, debug: bool) -> Self {
        self.pipeline = self.pipeline.with_debug(debug);
        self
    }

    pub fn build(self) -> PassPipeline {
        self.pipeline
    }
}

impl Default for PassPipelineBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::Program;
    use std::collections::BTreeMap;

    // Test pass that does nothing
    struct NoOpPass;

    impl Pass for NoOpPass {
        fn name(&self) -> &'static str {
            "noop"
        }

        fn run(&mut self, _program: &mut Program) -> PassResult {
            Ok(())
        }
    }

    // Test pass that always fails
    struct FailingPass;

    impl Pass for FailingPass {
        fn name(&self) -> &'static str {
            "failing"
        }

        fn run(&mut self, _program: &mut Program) -> PassResult {
            Err(PassError::Failed("intentional failure".to_string()))
        }
    }

    #[test]
    fn test_empty_pipeline() {
        let mut pipeline = PassPipeline::new();
        let mut program = Program {
            functions: BTreeMap::new(),
        };

        let result = pipeline.run(&mut program);
        assert!(result.is_ok());
    }

    #[test]
    fn test_successful_pipeline() {
        let mut pipeline = PassPipeline::new().add_pass(NoOpPass).add_pass(NoOpPass);

        let mut program = Program {
            functions: BTreeMap::new(),
        };

        let result = pipeline.run(&mut program);
        assert!(result.is_ok());
    }

    #[test]
    fn test_failing_pipeline() {
        let mut pipeline = PassPipeline::new().add_pass(NoOpPass).add_pass(FailingPass);

        let mut program = Program {
            functions: BTreeMap::new(),
        };

        let result = pipeline.run(&mut program);
        assert!(result.is_err());

        if let Err(PassError::Failed(msg)) = result {
            assert!(msg.contains("failing"));
            assert!(msg.contains("intentional failure"));
        } else {
            panic!("Expected PassError::Failed");
        }
    }

    #[test]
    fn test_pipeline_builder() {
        let pipeline = PassPipelineBuilder::new()
            .add_pass(NoOpPass)
            .debug(true)
            .build();

        assert_eq!(pipeline.pass_names(), vec!["noop"]);
    }

    #[test]
    fn test_default_pipeline() {
        let pipeline = PassPipeline::default_pipeline();
        let names = pipeline.pass_names();

        // Should contain the expected passes in order
        assert!(names.contains(&"inline"));
        assert!(names.contains(&"const_eval"));
        assert!(names.contains(&"ssa_repair"));
        assert!(names.contains(&"ast_to_ir"));
    }
}
