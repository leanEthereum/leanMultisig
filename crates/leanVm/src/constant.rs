use std::ops::Range;

use p3_field::extension::BinomialExtensionField;
use p3_koala_bear::KoalaBear;

use crate::memory::address::MemoryAddress;

/// The degree of the extension field.
pub const DIMENSION: usize = 8;

/// The base field of the zkVM.
pub(crate) type F = KoalaBear;

/// The extension field of the zkVM.
pub(crate) type EF = BinomialExtensionField<F, DIMENSION>;

// Memory segment IDs

/// Segment for public inputs and global constants.
pub const PUBLIC_DATA_SEGMENT: usize = 0;
/// Segment for the main stack (used by fp and ap).
pub const MAIN_STACK_SEGMENT: usize = 1;
/// Segment for runtime vector memory (for Poseidon, EF multiplication, etc.).
pub const VEC_RUNTIME_SEGMENT: usize = 2;
/// Segment for the compiled bytecode (where `pc` points).
pub const CODE_SEGMENT: usize = 3;

// Convention-based virtual memory pointers.

/// Points to `[0; DIMENSION]` in the vectorized memory segment.
pub const ZERO_VEC_PTR: MemoryAddress = MemoryAddress::new(VEC_RUNTIME_SEGMENT, 0);
/// Points to the result of `Poseidon2([0; 16])`, stored as 2 vector elements.
pub const POSEIDON_16_NULL_HASH_PTR: MemoryAddress = MemoryAddress::new(VEC_RUNTIME_SEGMENT, 1);
/// Points to the last 8 elements of `Poseidon2([0; 24])`, stored as 1 vector element.
pub const POSEIDON_24_NULL_HASH_PTR: MemoryAddress = MemoryAddress::new(VEC_RUNTIME_SEGMENT, 3);

/// Start of the public input memory region within the PUBLIC_DATA_SEGMENT.
pub const PUBLIC_INPUT_START: MemoryAddress = MemoryAddress::new(PUBLIC_DATA_SEGMENT, 0);

/// The maximum size of the memory.
pub const MAX_MEMORY_SIZE: usize = 1 << 23;

// Dot product constants

/// The total number of columns in the Dot Product AIR.
pub(crate) const DOT_PRODUCT_AIR_COLUMNS: usize = 9;
/// Defines column groups for processing.
pub(crate) const DOT_PRODUCT_AIR_COLUMN_GROUPS: [Range<usize>; 5] = [0..1, 1..2, 2..5, 5..8, 8..9];
