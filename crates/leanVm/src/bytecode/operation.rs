/// The basic arithmetic operations supported by the VM's `Computation` instruction.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Operation {
    /// Field addition in the base field.
    Add,
    /// Field multiplication in the base field.
    Mul,
}
