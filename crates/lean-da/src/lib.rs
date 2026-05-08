#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use backend::Proof;
use lean_compiler::{ProgramSource, compile_program};
use lean_prover::{
    default_whir_config,
    prove_execution::{ExecutionProof, prove_execution},
    verify_execution::verify_execution,
};
use lean_vm::{Bytecode, ExecutionWitness, F};

static EMBEDDED_ZK_DSL: include_dir::Dir<'_> = include_dir::include_dir!("$CARGO_MANIFEST_DIR/zkdsl_implem");

const STARTING_LOG_INV_RATE: usize = 1;

pub fn compile_lean_da_bytecode() -> Bytecode {
    let source = ProgramSource::Embedded {
        entry: "lean_da.py".to_string(),
        dir: &EMBEDDED_ZK_DSL,
    };
    compile_program(&source)
}

pub fn prove_lean_da(bytecode: &Bytecode, public_input: &[F]) -> ExecutionProof {
    let witness = ExecutionWitness::default();
    prove_execution(
        bytecode,
        public_input,
        &witness,
        &default_whir_config(STARTING_LOG_INV_RATE),
        false,
    )
    .unwrap()
}

pub fn verify_lean_da(bytecode: &Bytecode, public_input: &[F], proof: Proof<F>) {
    verify_execution(bytecode, public_input, proof).unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compile_prove_verify() {
        let bytecode = compile_lean_da_bytecode();
        let public_input: Vec<F> = vec![];
        let proof = prove_lean_da(&bytecode, &public_input);
        verify_lean_da(&bytecode, &public_input, proof.proof);
    }
}
