// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! NEON helpers shared by Poseidon1 permutations.

use core::arch::aarch64::{self, int32x4_t, uint32x4_t};
use core::mem::transmute;

use super::exp_small;
use crate::{FieldParameters, MontyParameters, PackedMontyField31Neon, PackedMontyParameters, RelativelyPrimePower};

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

/// Converts a scalar constant into a packed NEON vector in "negative form" (`c - P`).
#[inline(always)]
pub(crate) fn convert_to_vec_neg_form_neon<MP: MontyParameters>(input: i32) -> int32x4_t {
    unsafe {
        let input_sub_p = input - (MP::PRIME as i32);
        aarch64::vdupq_n_s32(input_sub_p)
    }
}

/// Performs the fused AddRoundConstant and S-Box operation `x -> (x + c)^D`.
///
/// `val` must contain elements in canonical form `[0, P)`.
/// `rc` must contain round constants in negative form `[-P, 0)`.
pub(crate) fn add_rc_and_sbox<PMP, const D: u64>(val: &mut PackedMontyField31Neon<PMP>, rc: int32x4_t)
where
    PMP: PackedMontyParameters + FieldParameters + RelativelyPrimePower<D>,
{
    unsafe {
        let vec_val_s = val.to_signed_vector();
        let val_plus_rc = aarch64::vaddq_s32(vec_val_s, rc);
        let output = exp_small::<PMP, D>(val_plus_rc);
        *val = PackedMontyField31Neon::<PMP>::from_vector(output);
    }
}
