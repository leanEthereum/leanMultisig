use std::fmt;

/// Describes the metadata for a precompiled function available to the zkVM.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Precompile {
    /// The unique identifier for the precompile.
    pub name: PrecompileName,
    /// The number of inputs.
    pub n_inputs: usize,
    /// The number of outputs.
    pub n_outputs: usize,
}

/// An enum representing the names of all available precompiles.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrecompileName {
    /// The Poseidon2 permutation over 16 field elements.
    Poseidon16,
    /// The Poseidon2 permutation over 24 field elements.
    Poseidon24,
    /// The dot product of two vectors of extension field elements.
    DotProduct,
    /// The evaluation of a multilinear polynomial.
    MultilinearEval,
}

impl PrecompileName {
    /// Returns the string representation of the precompile name.
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Poseidon16 => "poseidon16",
            Self::Poseidon24 => "poseidon24",
            Self::DotProduct => "dot_product",
            Self::MultilinearEval => "multilinear_eval",
        }
    }
}

impl fmt::Display for PrecompileName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Metadata for the Poseidon2 permutation over 16 elements.
pub const POSEIDON_16: Precompile = Precompile {
    name: PrecompileName::Poseidon16,
    n_inputs: 2,
    n_outputs: 1,
};

/// Metadata for the Poseidon2 permutation over 24 elements.
pub const POSEIDON_24: Precompile = Precompile {
    name: PrecompileName::Poseidon24,
    n_inputs: 2,
    n_outputs: 1,
};

/// Metadata for the dot product precompile.
pub const DOT_PRODUCT: Precompile = Precompile {
    name: PrecompileName::DotProduct,
    n_inputs: 4,
    n_outputs: 0,
};

/// Metadata for the multilinear evaluation precompile.
pub const MULTILINEAR_EVAL: Precompile = Precompile {
    name: PrecompileName::MultilinearEval,
    n_inputs: 4,
    n_outputs: 0,
};

/// An array containing the metadata for all supported precompiles.
pub const PRECOMPILES: [Precompile; 4] = [POSEIDON_16, POSEIDON_24, DOT_PRODUCT, MULTILINEAR_EVAL];
