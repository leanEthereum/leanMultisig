// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! NEON helpers shared by Poseidon1 permutations.

use core::arch::aarch64::{self, uint32x4_t};
use core::mem::transmute;

use super::exp_small;
use crate::{FieldParameters, PackedMontyField31Neon, PackedMontyParameters, RelativelyPrimePower};
use field::uint32x4_mod_add;

/// A specialized representation of the Poseidon state for a width of 16.
///
/// Splits the state into `s0` (undergoes S-box) and `s_hi` (undergoes only linear transforms),
/// enabling instruction-level parallelism between the two independent data paths.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct InternalLayer16<PMP: PackedMontyParameters> {
    pub(crate) s0: PackedMontyField31Neon<PMP>,
    pub(crate) s_hi: [uint32x4_t; 15],
}

impl<PMP: PackedMontyParameters> InternalLayer16<PMP> {
    #[inline]
    pub(crate) unsafe fn to_packed_field_array(self) -> [PackedMontyField31Neon<PMP>; 16] {
        unsafe { transmute(self) }
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_packed_field_array(vector: [PackedMontyField31Neon<PMP>; 16]) -> Self {
        unsafe { transmute(vector) }
    }
}

/// Converts a scalar constant into a packed NEON vector (canonical unsigned form).
#[inline(always)]
pub(crate) fn convert_to_vec_neon(input: u32) -> uint32x4_t {
    unsafe { aarch64::vdupq_n_u32(input) }
}

/// Performs the AddRoundConstant and S-Box operation `x -> (x + c)^D`.
///
/// `val` must contain elements in canonical form `[0, P)`.
/// `rc` must contain round constants in canonical form `[0, P)`.
pub(crate) fn add_rc_and_sbox<PMP, const D: u64>(val: &mut PackedMontyField31Neon<PMP>, rc: uint32x4_t)
where
    PMP: PackedMontyParameters + FieldParameters + RelativelyPrimePower<D>,
{
    unsafe {
        let val_plus_rc = uint32x4_mod_add(val.to_vector(), rc, PMP::PACKED_P);
        let output = exp_small::<PMP, D>(val_plus_rc);
        *val = PackedMontyField31Neon::<PMP>::from_vector(output);
    }
}
