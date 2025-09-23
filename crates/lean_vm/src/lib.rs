//! Lean VM - A minimal virtual machine implementation

pub mod core;
pub mod diagnostics;
pub mod execution;
pub mod isa;
pub mod witness;

pub use core::*;
pub use diagnostics::*;
pub use execution::*;
pub use isa::*;
pub use witness::*;

/// Main execution entry point for the VM
pub fn execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    source_code: &str,
    function_locations: &std::collections::BTreeMap<usize, String>,
    profiler: bool,
) -> ExecutionResult {
    execution::execute_bytecode_impl(
        bytecode,
        public_input,
        private_input,
        source_code,
        function_locations,
        profiler,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn test_vm_basic_functionality() {
        let bytecode = Bytecode::new(vec![]);
        let result = execute_bytecode(
            &bytecode,
            &[],
            &[],
            "",
            &std::collections::BTreeMap::new(),
            false,
        );
        assert!(result.is_success());
    }

    #[test]
    fn test_memory_operations() {
        let mut memory = Memory::empty();
        assert!(memory.set(0, F::from_usize(42)).is_ok());
        assert_eq!(memory.get(0).unwrap(), F::from_usize(42));
    }

    #[test]
    fn test_operation_compute() {
        use crate::isa::Operation;

        let add = Operation::Add;
        let mul = Operation::Mul;

        assert_eq!(
            add.compute(F::from_usize(2), F::from_usize(3)),
            F::from_usize(5)
        );
        assert_eq!(
            mul.compute(F::from_usize(2), F::from_usize(3)),
            F::from_usize(6)
        );
    }

    #[test]
    fn test_witness_creation() {
        let witness = WitnessPoseidon16::poseidon_of_zero();
        assert_eq!(witness.input, [F::ZERO; 16]);
    }
}
