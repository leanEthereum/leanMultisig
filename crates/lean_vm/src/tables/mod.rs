mod extension_op;
pub use extension_op::*;

mod poseidon_16;
pub use poseidon_16::*;

mod table_enum;
pub use table_enum::*;

mod table_trait;
pub use table_trait::*;

mod execution;
pub use execution::*;

mod utils;
pub(crate) use utils::*;

// `PRECOMPILE_DATA` is the bus discriminator separating the two precompile
// tables. Disjointness is by parity of bit 0:
//
//   Poseidon16  (odd):  1 + 2·flag_half + 4·flag_left + 8·flag_left·offset_left
//   ExtensionOp (even): 4·is_be + 8·flag_add + 16·flag_mul + 32·flag_poly_eq + 64·len
//
// Multiplying `offset_left` by `flag_left` is needed for soundness: see 3.4.1 in minimal_zkVM.pdf
