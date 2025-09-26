pub mod simplify;
pub mod transformations;
pub mod types;
pub mod unroll;
pub mod utilities;

pub use types::{ConstMalloc, SimpleFunction, SimpleLine, SimpleProgram, VarOrConstMallocAccess};

use crate::lang::Program;
use std::collections::BTreeMap;
use types::{ArrayManager, Counters};

/// Main entry point for program simplification.
pub fn simplify_program(mut program: Program) -> SimpleProgram {
    transformations::handle_inlined_functions(&mut program);
    transformations::handle_const_arguments(&mut program);
    let mut new_functions = BTreeMap::new();
    let mut counters = Counters::default();
    let mut const_malloc = ConstMalloc::default();

    for (name, func) in &program.functions {
        let mut array_manager = ArrayManager::default();
        let simplified_instructions = simplify::simplify_lines(
            &func.body,
            &mut counters,
            &mut new_functions,
            false,
            &mut array_manager,
            &mut const_malloc,
        );
        let arguments = func
            .arguments
            .iter()
            .map(|(v, is_const)| {
                assert!(!is_const,);
                v.clone()
            })
            .collect::<Vec<_>>();
        new_functions.insert(
            name.clone(),
            SimpleFunction {
                name: name.clone(),
                arguments,
                n_returned_vars: func.n_returned_vars,
                instructions: simplified_instructions,
            },
        );
        const_malloc.map.clear();
    }
    SimpleProgram {
        functions: new_functions,
    }
}
