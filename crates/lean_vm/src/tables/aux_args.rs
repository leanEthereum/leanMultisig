use backend::PrimeCharacteristicRing;

use crate::F;

pub(super) const POSEIDON_16_PRECOMPILE_ENCODING_BIT_IS_COMPRESSION: usize = 0;
pub(super) const POSEIDON_16_PRECOMPILE_ENCODING_BIT_IS_PERMUTATION: usize = 1;
pub(super) const EXTENSION_PRECOMPILE_ENCODING_BIT_IS_BE: usize = 2;
pub(super) const EXTENSION_PRECOMPILE_ENCODING_BIT_ADD: usize = 3;
pub(super) const EXTENSION_PRECOMPILE_ENCODING_BIT_DOT_PRODUCT: usize = 4;
pub(super) const EXTENSION_PRECOMPILE_ENCODING_BIT_POLY_EQ: usize = 5;
pub(super) const EXTENSION_PRECOMPILE_ENCODING_BIT_SIZE: usize = 6;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PrecompileAuxArg {
    Poseidon16(PoseidonMode),
    Extension(ExtensionPrecompileAuxArgs),
}

impl PrecompileAuxArg {
    /// should be injective
    pub fn encoding_precompile_data(&self) -> F {
        match self {
            PrecompileAuxArg::Poseidon16(mode) => poseidon16_precompile_data(*mode),
            PrecompileAuxArg::Extension(args) => extension_op_precompile_data(args),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum PoseidonMode {
    Permutation,
    #[default]
    Compression,
}

impl PoseidonMode {
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "poseidon16_permute" => Some(Self::Permutation),
            "poseidon16_compress" => Some(Self::Compression),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExtensionPrecompileAuxArgs {
    pub field: ExtensionPrecompileField,
    pub op: ExtensionPrecompileMode,
    pub size: usize,
}

impl ExtensionPrecompileAuxArgs {
    /// return an empty size (should be filled later)
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "add_ee" => Some(Self {
                field: ExtensionPrecompileField::EE,
                op: ExtensionPrecompileMode::Add,
                size: 0,
            }),
            "add_be" => Some(Self {
                field: ExtensionPrecompileField::BE,
                op: ExtensionPrecompileMode::Add,
                size: 0,
            }),
            "dot_product_ee" => Some(Self {
                field: ExtensionPrecompileField::EE,
                op: ExtensionPrecompileMode::DotProduct,
                size: 0,
            }),
            "dot_product_be" => Some(Self {
                field: ExtensionPrecompileField::BE,
                op: ExtensionPrecompileMode::DotProduct,
                size: 0,
            }),
            "poly_eq_ee" => Some(Self {
                field: ExtensionPrecompileField::EE,
                op: ExtensionPrecompileMode::PolyEq,
                size: 0,
            }),
            "poly_eq_be" => Some(Self {
                field: ExtensionPrecompileField::BE,
                op: ExtensionPrecompileMode::PolyEq,
                size: 0,
            }),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExtensionPrecompileField {
    EE, // extension - extension
    BE, // base - extension
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExtensionPrecompileMode {
    Add,        // a1 + b1 + a2 + b2 + ...
    DotProduct, // a1*b1 + a2*b2 + ...
    PolyEq,     // (a1*b1 + (1-a1)*(1-b1)) * (a2*b2 + (1-a2)*(1-b2)) * ...
}

pub fn poseidon16_precompile_data(mode: PoseidonMode) -> F {
    match mode {
        PoseidonMode::Permutation => F::from_usize(1 << POSEIDON_16_PRECOMPILE_ENCODING_BIT_IS_PERMUTATION),
        PoseidonMode::Compression => F::from_usize(1 << POSEIDON_16_PRECOMPILE_ENCODING_BIT_IS_COMPRESSION),
    }
}

pub fn extension_op_precompile_data(args: &ExtensionPrecompileAuxArgs) -> F {
    let op_bit = match args.op {
        ExtensionPrecompileMode::Add => 1 << EXTENSION_PRECOMPILE_ENCODING_BIT_ADD,
        ExtensionPrecompileMode::DotProduct => 1 << EXTENSION_PRECOMPILE_ENCODING_BIT_DOT_PRODUCT,
        ExtensionPrecompileMode::PolyEq => 1 << EXTENSION_PRECOMPILE_ENCODING_BIT_POLY_EQ,
    };
    let is_be = (args.field == ExtensionPrecompileField::BE) as usize;
    F::from_usize(
        (is_be << EXTENSION_PRECOMPILE_ENCODING_BIT_IS_BE)
            + op_bit
            + (args.size << EXTENSION_PRECOMPILE_ENCODING_BIT_SIZE),
    )
}

#[test]
fn soundness_precompile_table_unique_argument_encoding() {
    use backend::Field;
    let max_log_n_rows = crate::MAX_LOG_N_ROWS_PER_TABLE
        .iter()
        .find(|(table, _)| *table == crate::Table::extension_op())
        .unwrap()
        .1;
    assert!(EXTENSION_PRECOMPILE_ENCODING_BIT_SIZE + max_log_n_rows < crate::F::bits());
}
