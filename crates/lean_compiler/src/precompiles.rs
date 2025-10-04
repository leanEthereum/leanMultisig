use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Precompile {
    pub name: PrecompileName,
    pub n_inputs: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrecompileName {
    Poseidon16,
    Poseidon24,
    DotProduct,
    MultilinearEval,
}

impl Display for PrecompileName {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Poseidon16 => write!(f, "poseidon16"),
            Self::Poseidon24 => write!(f, "poseidon24"),
            Self::DotProduct => write!(f, "dot_product"),
            Self::MultilinearEval => write!(f, "multilinear_eval"),
        }
    }
}

pub const POSEIDON_16: Precompile = Precompile {
    name: PrecompileName::Poseidon16,
    n_inputs: 4,
};

pub const POSEIDON_24: Precompile = Precompile {
    name: PrecompileName::Poseidon24,
    n_inputs: 3,
};

pub const DOT_PRODUCT: Precompile = Precompile {
    name: PrecompileName::DotProduct,
    n_inputs: 4,
};

pub const MULTILINEAR_EVAL: Precompile = Precompile {
    name: PrecompileName::MultilinearEval,
    n_inputs: 4,
};

pub const PRECOMPILES: [Precompile; 4] = [POSEIDON_16, POSEIDON_24, DOT_PRODUCT, MULTILINEAR_EVAL];
