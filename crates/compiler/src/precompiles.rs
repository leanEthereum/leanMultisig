use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Precompile {
    pub name: PrecompileName,
    pub n_inputs: usize,
    pub n_outputs: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrecompileName {
    Poseidon16,
    Poseidon24,
    DotProduct,
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

pub(crate) const POSEIDON_16: Precompile = Precompile {
    name: PrecompileName::Poseidon16,
    n_inputs: 2,
    n_outputs: 1,
};

pub(crate) const POSEIDON_24: Precompile = Precompile {
    name: PrecompileName::Poseidon24,
    n_inputs: 2,
    n_outputs: 1,
};

pub(crate) const DOT_PRODUCT: Precompile = Precompile {
    name: PrecompileName::DotProduct,
    n_inputs: 4,
    n_outputs: 0,
};

pub(crate) const MULTILINEAR_EVAL: Precompile = Precompile {
    name: PrecompileName::MultilinearEval,
    n_inputs: 4,
    n_outputs: 0,
};

pub const PRECOMPILES: [Precompile; 4] = [POSEIDON_16, POSEIDON_24, DOT_PRODUCT, MULTILINEAR_EVAL];
