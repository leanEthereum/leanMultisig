use crate::precompiles::dot_product::vm_exec::exec_dot_product;
use crate::{
    Bus, ColIndex, EF, ExtensionFieldLookupIntoMemory, F, LookupIntoMemory, Memory, ModularPrecompile, PrecompileTrace, RunnerError, Table, VectorLookupIntoMemory
};
use multilinear_toolkit::prelude::*;
pub use witness::*;

mod witness;

mod air;
pub use air::*;

mod vm_exec;

#[derive(Debug)]
pub struct DotProductPrecompile;

impl ModularPrecompile for DotProductPrecompile {
    type Witness = WitnessDotProduct;

    fn name() -> &'static str {
        "dot_product"
    }

    fn identifier() -> Table {
        Table::DotProduct
    }

    fn commited_columns() -> &'static [ColIndex] {
        &[]
    }

    fn simple_lookups() -> &'static [LookupIntoMemory] {
        &[]
    }

    fn ext_field_lookups() -> &'static [ExtensionFieldLookupIntoMemory] {
        &[]
    }

    fn vector_lookups() -> &'static [VectorLookupIntoMemory] {
        &[]
    }

    fn buses() -> &'static [Bus] {
        &[]
    }

    fn execute(
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        memory: &mut Memory,
    ) -> Result<Self::Witness, RunnerError> {
        exec_dot_product(arg_a, arg_b, arg_c, aux, memory)
    }

    fn gen_trace(witness: &[Self::Witness]) -> ProofResult<PrecompileTrace> {
        Ok(PrecompileTrace {
            base: vec![vec![F::ZERO; witness.len()]],
            ext: vec![vec![EF::ZERO; witness.len()]],
        })
    }

    fn air_padding_row() -> Vec<EF> {
        vec![
            EF::ONE,  // StartFlag
            EF::ONE,  // Len
            EF::ZERO, // IndexA
            EF::ZERO, // IndexB
            EF::ZERO, // Computation
        ]
    }
}
