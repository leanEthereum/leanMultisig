// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! A collection of helper methods when AVX2 is available

#[cfg(target_feature = "avx512f")]
use core::arch::x86_64::__m512i;
use core::arch::x86_64::{self, __m128i, __m256i};
use core::mem::transmute;

// Modular addition/subtraction for P < 2^32.
//
// For add: t = a + b (wrapping u32). If overflow occurred or t >= P, subtract P.
// Overflow detection: t < a (unsigned) means carry.
//
// For sub: t = a - b (wrapping u32). If borrow (a < b), add P.
// These algorithms work for any P < 2^32.

/// Add the packed vectors `a` and `b` modulo `p` (SSE, 4 elements).
///
/// Assumes `a, b` in `[0, P)` where `P < 2^32`. Works for P > 2^31.
#[inline(always)]
#[must_use]
fn mm128_mod_add(a: __m128i, b: __m128i, p: __m128i) -> __m128i {
    unsafe {
        let t = x86_64::_mm_add_epi32(a, b);
        let u = x86_64::_mm_sub_epi32(t, p);
        // Detect carry: flip sign bits for unsigned comparison
        let flip = x86_64::_mm_set1_epi32(i32::MIN);
        let a_f = x86_64::_mm_xor_si128(a, flip);
        let t_f = x86_64::_mm_xor_si128(t, flip);
        let overflow = x86_64::_mm_cmpgt_epi32(a_f, t_f); // a > t unsigned → overflow
        let t_f2 = t_f; // reuse
        let p_m1_f = x86_64::_mm_xor_si128(x86_64::_mm_sub_epi32(p, x86_64::_mm_set1_epi32(1)), flip);
        let geq_p = x86_64::_mm_cmpgt_epi32(t_f2, p_m1_f); // t > p-1 unsigned → t >= p
        let mask = x86_64::_mm_or_si128(overflow, geq_p);
        // blend: (mask & u) | (~mask & t)
        let sel_u = x86_64::_mm_and_si128(mask, u);
        let sel_t = x86_64::_mm_andnot_si128(mask, t);
        x86_64::_mm_or_si128(sel_u, sel_t)
    }
}

/// Subtract the packed vectors `a` and `b` modulo `p` (SSE, 4 elements).
///
/// Assumes `a, b` in `[0, P)` where `P < 2^32`. Works for P > 2^31.
#[inline(always)]
#[must_use]
fn mm128_mod_sub(a: __m128i, b: __m128i, p: __m128i) -> __m128i {
    unsafe {
        let t = x86_64::_mm_sub_epi32(a, b);
        // Detect borrow: b > a unsigned
        let flip = x86_64::_mm_set1_epi32(i32::MIN);
        let a_f = x86_64::_mm_xor_si128(a, flip);
        let b_f = x86_64::_mm_xor_si128(b, flip);
        let borrow = x86_64::_mm_cmpgt_epi32(b_f, a_f);
        let corr = x86_64::_mm_and_si128(borrow, p);
        x86_64::_mm_add_epi32(t, corr)
    }
}

/// Add the packed vectors `lhs` and `rhs` modulo `p` (AVX2, 8 elements).
///
/// Assumes `a, b` in `[0, P)` where `P < 2^32`. Works for P > 2^31.
#[inline(always)]
#[must_use]
pub fn mm256_mod_add(lhs: __m256i, rhs: __m256i, p: __m256i) -> __m256i {
    unsafe {
        let t = x86_64::_mm256_add_epi32(lhs, rhs);
        let u = x86_64::_mm256_sub_epi32(t, p);
        let flip = x86_64::_mm256_set1_epi32(i32::MIN);
        let lhs_f = x86_64::_mm256_xor_si256(lhs, flip);
        let t_f = x86_64::_mm256_xor_si256(t, flip);
        let overflow = x86_64::_mm256_cmpgt_epi32(lhs_f, t_f);
        let p_m1_f = x86_64::_mm256_xor_si256(x86_64::_mm256_sub_epi32(p, x86_64::_mm256_set1_epi32(1)), flip);
        let geq_p = x86_64::_mm256_cmpgt_epi32(t_f, p_m1_f);
        let mask = x86_64::_mm256_or_si256(overflow, geq_p);
        x86_64::_mm256_blendv_epi8(t, u, mask)
    }
}

/// Subtract the packed vectors `lhs` and `rhs` modulo `p` (AVX2, 8 elements).
///
/// Assumes `a, b` in `[0, P)` where `P < 2^32`. Works for P > 2^31.
#[inline(always)]
#[must_use]
pub fn mm256_mod_sub(lhs: __m256i, rhs: __m256i, p: __m256i) -> __m256i {
    unsafe {
        let t = x86_64::_mm256_sub_epi32(lhs, rhs);
        let flip = x86_64::_mm256_set1_epi32(i32::MIN);
        let lhs_f = x86_64::_mm256_xor_si256(lhs, flip);
        let rhs_f = x86_64::_mm256_xor_si256(rhs, flip);
        let borrow = x86_64::_mm256_cmpgt_epi32(rhs_f, lhs_f);
        let corr = x86_64::_mm256_and_si256(borrow, p);
        x86_64::_mm256_add_epi32(t, corr)
    }
}

#[cfg(target_feature = "avx512f")]
/// Add the packed vectors `lhs` and `rhs` modulo `p` (AVX-512, 16 elements).
///
/// Assumes `a, b` in `[0, P)` where `P < 2^32`. Works for P > 2^31.
#[inline(always)]
#[must_use]
pub fn mm512_mod_add(lhs: __m512i, rhs: __m512i, p: __m512i) -> __m512i {
    unsafe {
        let t = x86_64::_mm512_add_epi32(lhs, rhs);
        let u = x86_64::_mm512_sub_epi32(t, p);
        // AVX-512 has native unsigned comparison
        let overflow = x86_64::_mm512_cmplt_epu32_mask(t, lhs); // t < lhs → overflow
        let geq_p = x86_64::_mm512_cmpge_epu32_mask(t, p); // t >= P
        let mask = overflow | geq_p;
        x86_64::_mm512_mask_mov_epi32(t, mask, u)
    }
}

#[cfg(target_feature = "avx512f")]
/// Subtract the packed vectors `lhs` and `rhs` modulo `p` (AVX-512, 16 elements).
///
/// Assumes `a, b` in `[0, P)` where `P < 2^32`. Works for P > 2^31.
#[inline(always)]
#[must_use]
pub fn mm512_mod_sub(lhs: __m512i, rhs: __m512i, p: __m512i) -> __m512i {
    unsafe {
        let t = x86_64::_mm512_sub_epi32(lhs, rhs);
        let borrow = x86_64::_mm512_cmplt_epu32_mask(lhs, rhs); // lhs < rhs → borrow
        let p_masked = x86_64::_mm512_maskz_mov_epi32(borrow, p);
        x86_64::_mm512_add_epi32(t, p_masked)
    }
}

/// Add two arrays of integers modulo `P` using packings.
///
/// Assumes `a, b` are in `[0, P)` where `P < 2^32`. Works for P > 2^31.
///
/// TODO: Add support for extensions of degree 2,3,6,7.
#[inline(always)]
pub fn packed_mod_add<const WIDTH: usize>(
    a: &[u32; WIDTH],
    b: &[u32; WIDTH],
    res: &mut [u32; WIDTH],
    p: u32,
    scalar_add: fn(u32, u32) -> u32,
) {
    match WIDTH {
        1 => res[0] = scalar_add(a[0], b[0]),
        4 => {
            // Perfectly fits into a m128i vector. The compiler is good at
            // optimising this into AVX2 instructions in cases where we need to
            // do multiple additions.
            let out: [u32; 4] = unsafe {
                let a: __m128i = transmute([a[0], a[1], a[2], a[3]]);
                let b: __m128i = transmute([b[0], b[1], b[2], b[3]]);
                let p: __m128i = x86_64::_mm_set1_epi32(p as i32);
                transmute(mm128_mod_add(a, b, p))
            };

            res.copy_from_slice(&out);
        }
        5 => {
            // We fit what we can into a m128i vector. The final add on
            // is done using a scalar addition. This seems to be faster than
            // trying to fit everything into an m256i vector and makes it much
            // easier for the compiler to optimise in cases where it needs to
            // do multiple additions.
            let out: [u32; 4] = unsafe {
                let a: __m128i = transmute([a[0], a[1], a[2], a[3]]);
                let b: __m128i = transmute([b[0], b[1], b[2], b[3]]);
                let p: __m128i = x86_64::_mm_set1_epi32(p as i32);
                transmute(mm128_mod_add(a, b, p))
            };
            res[4] = scalar_add(a[4], b[4]);

            res[..4].copy_from_slice(&out[..4]);
        }
        8 => {
            // This perfectly fits into a single m256i vector.
            let out: [u32; 8] = unsafe {
                let a: __m256i = transmute([a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]]);
                let b: __m256i = transmute([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]);
                let p: __m256i = x86_64::_mm256_set1_epi32(p as i32);
                transmute(mm256_mod_add(a, b, p))
            };

            res.copy_from_slice(&out);
        }
        _ => panic!("Currently unsupported width for packed addition."),
    }
}

/// Subtract two arrays of integers modulo `P` using packings.
///
/// Assumes `a, b` are in `[0, P)` where `P < 2^32`. Works for P > 2^31.
///
/// TODO: Add support for extensions of degree 2,3,6,7.
#[inline(always)]
pub fn packed_mod_sub<const WIDTH: usize>(
    a: &[u32; WIDTH],
    b: &[u32; WIDTH],
    res: &mut [u32; WIDTH],
    p: u32,
    scalar_sub: fn(u32, u32) -> u32,
) {
    match WIDTH {
        1 => res[0] = scalar_sub(a[0], b[0]),
        4 => {
            // Perfectly fits into a m128i vector. The compiler is good at
            // optimising this into AVX2 instructions in cases where we need to
            // do multiple additions.
            let out: [u32; 4] = unsafe {
                let a: __m128i = transmute([a[0], a[1], a[2], a[3]]);
                let b: __m128i = transmute([b[0], b[1], b[2], b[3]]);
                let p: __m128i = x86_64::_mm_set1_epi32(p as i32);
                transmute(mm128_mod_sub(a, b, p))
            };

            res.copy_from_slice(&out);
        }
        5 => {
            // We fit what we can into a m128i vector. The final add on
            // is done using a scalar subtraction. This seems to be faster than
            // trying to fit everything into an m256i vector and makes it much
            // easier for the compiler to optimise in cases where it needs to
            // do multiple additions.
            let out: [u32; 4] = unsafe {
                let a: __m128i = transmute([a[0], a[1], a[2], a[3]]);
                let b: __m128i = transmute([b[0], b[1], b[2], b[3]]);
                let p: __m128i = x86_64::_mm_set1_epi32(p as i32);
                transmute(mm128_mod_sub(a, b, p))
            };
            res[4] = scalar_sub(a[4], b[4]);

            res[..4].copy_from_slice(&out[..4]);
        }
        8 => {
            // This perfectly fits into a single m256i vector.
            let out: [u32; 8] = unsafe {
                let a: __m256i = transmute([a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]]);
                let b: __m256i = transmute([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]);
                let p: __m256i = x86_64::_mm256_set1_epi32(p as i32);
                transmute(mm256_mod_sub(a, b, p))
            };

            res.copy_from_slice(&out);
        }
        _ => panic!("Currently unsupported width for packed subtraction."),
    }
}
