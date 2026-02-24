use backend::{AirBuilder, PrimeCharacteristicRing};

use crate::constants::BITS_PER_LIMB;

/// Pack a collection of bits into a number (little-endian).
///
/// Given `vec = [v_0, v_1, ..., v_n]` returns `v_0 + 2*v_1 + ... + 2^n * v_n`
#[inline]
pub fn pack_bits_le<R: PrimeCharacteristicRing, I: DoubleEndedIterator<Item = R>>(iter: I) -> R {
    iter.rev().reduce(|acc, elem| acc.double() + elem).unwrap_or(R::ZERO)
}

/// Convert a 32-bit integer into an array of 32 boolean field elements (little-endian).
#[inline]
pub fn u32_to_bits_le<R: PrimeCharacteristicRing>(val: u32) -> [R; 32] {
    core::array::from_fn(|i| R::from_bool(val & (1 << i) != 0))
}

/// Verify that `a = b + c mod 2^32`
///
/// We assume that a, b, c are all given as 2 16-bit limbs and
/// each 16-bit limb has been range checked to be in `[0, 2^16)`.
#[inline]
pub fn add2<AB: AirBuilder>(builder: &mut AB, a: &[AB::F; 2], b: &[AB::F; 2], c: &[AB::F; 2]) {
    let two_16 = AB::F::from_u32(1 << 16);
    let two_32 = two_16.square();

    let acc_16 = a[0].clone() - b[0].clone() - c[0].clone();
    let acc_32 = a[1].clone() - b[1].clone() - c[1].clone();
    let acc = acc_16.clone() + acc_32 * two_16.clone();

    builder.assert_zero(acc.clone() * (acc.clone() + two_32.clone()));
    builder.assert_zero(acc_16.clone() * (acc_16 + two_16));
}

/// Verify that `a = b + c + d mod 2^32`
///
/// We assume that a, b, c, d are all given as 2 16-bit limbs and
/// each 16-bit limb has been range checked to be in `[0, 2^16)`.
#[inline]
pub fn add3<AB: AirBuilder>(builder: &mut AB, a: &[AB::F; 2], b: &[AB::F; 2], c: &[AB::F; 2], d: &[AB::F; 2]) {
    let two_16 = AB::F::from_u32(1 << 16);
    let two_32 = two_16.square();

    let acc_16 = a[0].clone() - b[0].clone() - c[0].clone() - d[0].clone();
    let acc_32 = a[1].clone() - b[1].clone() - c[1].clone() - d[1].clone();
    let acc = acc_16.clone() + acc_32 * two_16.clone();

    builder.assert_zero(acc.clone() * (acc.clone() + two_32.clone()) * (acc + two_32.double()));
    builder.assert_zero(acc_16.clone() * (acc_16.clone() + two_16.clone()) * (acc_16 + two_16.double()));
}

/// Verify that `a = (b ^ (c << shift))`
///
/// We assume that a is given as 2 16-bit limbs and both b and c are unpacked into 32 individual bits.
/// We assume that the bits of b have been range checked but not the inputs in c or a.
#[inline]
pub fn xor_32_shift<AB: AirBuilder>(builder: &mut AB, a: &[AB::F; 2], b: &[AB::F; 32], c: &[AB::F; 32], shift: usize) {
    // Range check all elements of c.
    for bit in c {
        builder.assert_bool(bit.clone());
    }

    // Compute (b ^ (c << shift)) and pack the result into two 16-bit integers.
    let xor_shift_c_0_16 = b[..BITS_PER_LIMB]
        .iter()
        .enumerate()
        .map(|(i, elem)| elem.clone().xor(&c[(32 + i - shift) % 32].clone()));
    let sum_0_16: AB::F = pack_bits_le(xor_shift_c_0_16);

    let xor_shift_c_16_32 = b[BITS_PER_LIMB..]
        .iter()
        .enumerate()
        .map(|(i, elem)| elem.clone().xor(&c[(32 + (i + BITS_PER_LIMB) - shift) % 32].clone()));
    let sum_16_32: AB::F = pack_bits_le(xor_shift_c_16_32);

    builder.assert_zero(a[0].clone() - sum_0_16);
    builder.assert_zero(a[1].clone() - sum_16_32);
}
