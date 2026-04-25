// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! AVX512 helpers shared by Poseidon1 permutations.

use core::arch::x86_64::{self, __m512i};
use core::mem::transmute;

use super::{apply_func_to_even_odd, packed_exp_3, packed_exp_5, packed_exp_7};
use crate::{MontyParameters, PackedMontyField31AVX512, PackedMontyParameters};

/// A specialized representation of the Poseidon state for a width of 16.
///
/// Splits the state into `s0` (undergoes S-box) and `s_hi` (undergoes only linear transforms),
/// enabling instruction-level parallelism between the two independent data paths.
#[derive(Clone, Copy)]
#[repr(C)]
pub struct InternalLayer16<PMP: PackedMontyParameters> {
    pub(crate) s0: PackedMontyField31AVX512<PMP>,
    pub(crate) s_hi: [__m512i; 15],
}

impl<PMP: PackedMontyParameters> InternalLayer16<PMP> {
    #[inline]
    pub(crate) unsafe fn to_packed_field_array(self) -> [PackedMontyField31AVX512<PMP>; 16] {
        unsafe { transmute(self) }
    }

    #[inline]
    #[must_use]
    pub(crate) fn from_packed_field_array(vector: [PackedMontyField31AVX512<PMP>; 16]) -> Self {
        unsafe { transmute(vector) }
    }
}

/// Use hard coded methods to compute `x -> x^D` for the even index entries and small `D`.
/// Inputs should be signed 32-bit integers in `[-P, ..., P]`.
/// Outputs will also be signed integers in `(-P, ..., P)` stored in the odd indices.
#[inline(always)]
#[must_use]
pub(crate) fn exp_small<PMP: PackedMontyParameters, const D: u64>(val: __m512i) -> __m512i {
    match D {
        3 => packed_exp_3::<PMP>(val),
        5 => packed_exp_5::<PMP>(val),
        7 => packed_exp_7::<PMP>(val),
        _ => panic!("No exp function for given D"),
    }
}

/// Converts a scalar constant into a packed AVX512 vector in "negative form" (`c - P`).
#[inline(always)]
pub(crate) fn convert_to_vec_neg_form<MP: MontyParameters>(input: i32) -> __m512i {
    let input_sub_p = input - (MP::PRIME as i32);
    unsafe { x86_64::_mm512_set1_epi32(input_sub_p) }
}

/// Performs the fused AddRoundConstant and S-Box operation `x -> (x + c)^D`.
///
/// `val` must contain elements in canonical form `[0, P)`.
/// `rc` must contain round constants in negative form `[-P, 0)`.
#[inline(always)]
pub(crate) fn add_rc_and_sbox<PMP: PackedMontyParameters, const D: u64>(
    val: &mut PackedMontyField31AVX512<PMP>,
    rc: __m512i,
) {
    unsafe {
        let vec_val = val.to_vector();
        let val_plus_rc = x86_64::_mm512_add_epi32(vec_val, rc);
        let output = apply_func_to_even_odd::<PMP>(val_plus_rc, exp_small::<PMP, D>);
        *val = PackedMontyField31AVX512::<PMP>::from_vector(output);
    }
}

/// Applies the S-Box `x -> x^D` to a packed vector. Output is in canonical form.
#[inline(always)]
pub(crate) fn sbox<PMP: PackedMontyParameters, const D: u64>(
    val: PackedMontyField31AVX512<PMP>,
) -> PackedMontyField31AVX512<PMP> {
    unsafe {
        let vec = val.to_vector();
        let out = apply_func_to_even_odd::<PMP>(vec, exp_small::<PMP, D>);
        PackedMontyField31AVX512::<PMP>::from_vector(out)
    }
}
