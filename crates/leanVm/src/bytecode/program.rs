use super::Bytecode;
use crate::constant::F;

/// Represents a program to be executed by the zkVM.
#[derive(Debug, Clone, Default)]
pub struct Program {
    /// The compiled instructions and hints for the program.
    pub bytecode: Bytecode,
    /// The public inputs for this specific execution.
    pub public_input: Vec<F>,
    /// The private (witness) inputs for this specific execution.
    pub private_input: Vec<F>,
}
