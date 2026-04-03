// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! A collection of helper methods when Neon is available

use core::arch::aarch64::{self, uint32x4_t};
use core::mem::transmute;

/// Convert a four element array of u32's into a packed vector.
///
/// This will be a no-op.
#[inline(always)]
fn array_to_uint32x4(input: [u32; 4]) -> uint32x4_t {
    // Safety: `[u32; 4]` has the same size as `uint32x4_t`.
    unsafe { transmute::<[u32; 4], uint32x4_t>(input) }
}

/// Convert a packed vector into a four element array of u32's.
///
/// This will be a no-op.
#[inline(always)]
fn uint32x4_to_array(input: uint32x4_t) -> [u32; 4] {
    // Safety: `[u32; 4]` has the same size and alignment as `uint32x4_t`.
    unsafe { transmute::<uint32x4_t, [u32; 4]>(input) }
}

/// Add the packed vectors `a` and `b` modulo `p`.
///
/// Assumes `a, b` are in `[0, P)` where `P < 2^32`. The result will be in `[0, P)`.
/// Works for any P < 2^32, including P > 2^31 where a + b may overflow u32.
#[inline]
#[must_use]
pub fn uint32x4_mod_add(a: uint32x4_t, b: uint32x4_t, p: uint32x4_t) -> uint32x4_t {
    // Algorithm: t = a + b (wrapping). u = t - P (wrapping).
    // If a + b overflowed u32 OR t >= P, use u; otherwise use t.
    // Overflow detection: t < a (unsigned) means carry occurred.
    //
    //      add       t.4s, a.4s, b.4s
    //      sub       u.4s, t.4s, P.4s
    //      cmhi      overflow.4s, a.4s, t.4s     // carry: a > t (unsigned)
    //      cmhs      geq_p.4s, t.4s, P.4s        // t >= P (unsigned)
    //      orr       mask.4s, overflow.4s, geq_p.4s
    //      bsl       mask.4s, u.4s, t.4s
    // throughput: 1.5 cyc/vec (2.67 els/cyc)
    // latency: 8 cyc
    unsafe {
        let t = aarch64::vaddq_u32(a, b);
        let u = aarch64::vsubq_u32(t, p);
        let overflow = aarch64::vcgtq_u32(a, t); // a > t means overflow
        let geq_p = aarch64::vcgeq_u32(t, p); // t >= P means need reduction
        let mask = aarch64::vorrq_u32(overflow, geq_p);
        aarch64::vbslq_u32(mask, u, t) // if mask then u else t
    }
}

/// Subtract the packed vectors `a` and `b` modulo `p`.
///
/// Assumes `a, b` are in `[0, P)` where `P < 2^32`. The result will be in `[0, P)`.
/// Works for any P < 2^32, including P > 2^31.
#[inline]
#[must_use]
pub fn uint32x4_mod_sub(a: uint32x4_t, b: uint32x4_t, p: uint32x4_t) -> uint32x4_t {
    // Algorithm: t = a - b (wrapping). If a < b (borrow), result = t + P; otherwise result = t.
    //
    //      sub       t.4s, a.4s, b.4s
    //      cmhi      borrow.4s, b.4s, a.4s        // b > a means borrow
    //      and       corr.4s, borrow.4s, P.4s
    //      add       res.4s, t.4s, corr.4s
    // throughput: 1 cyc/vec (4 els/cyc)
    // latency: 8 cyc
    unsafe {
        let t = aarch64::vsubq_u32(a, b);
        let borrow = aarch64::vcgtq_u32(b, a); // b > a means borrow
        let corr = aarch64::vandq_u32(borrow, p);
        aarch64::vaddq_u32(t, corr)
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
            // Perfectly fits into a uint32x4_t vector.
            let out: [u32; 4] = unsafe {
                let a = array_to_uint32x4([a[0], a[1], a[2], a[3]]);
                let b = array_to_uint32x4([b[0], b[1], b[2], b[3]]);
                let p: uint32x4_t = aarch64::vdupq_n_u32(p);
                uint32x4_to_array(uint32x4_mod_add(a, b, p))
            };

            res.copy_from_slice(&out);
        }
        5 => {
            // We fit what we can into a uint32x4_t element.
            // The final add is done using a scalar addition.
            let out: [u32; 4] = unsafe {
                let a = array_to_uint32x4([a[0], a[1], a[2], a[3]]);
                let b = array_to_uint32x4([b[0], b[1], b[2], b[3]]);
                let p: uint32x4_t = aarch64::vdupq_n_u32(p);
                uint32x4_to_array(uint32x4_mod_add(a, b, p))
            };

            res[4] = scalar_add(a[4], b[4]);

            res[..4].copy_from_slice(&out);
        }
        8 => {
            // This perfectly fits into two uint32x4_t elements.
            let (out_lo, out_hi): ([u32; 4], [u32; 4]) = unsafe {
                let p: uint32x4_t = aarch64::vdupq_n_u32(p);

                let a_lo = array_to_uint32x4([a[0], a[1], a[2], a[3]]);
                let b_lo = array_to_uint32x4([b[0], b[1], b[2], b[3]]);
                let out_lo = uint32x4_to_array(uint32x4_mod_add(a_lo, b_lo, p));

                let a_hi = array_to_uint32x4([a[4], a[5], a[6], a[7]]);
                let b_hi = array_to_uint32x4([b[4], b[5], b[6], b[7]]);
                let out_hi = uint32x4_to_array(uint32x4_mod_add(a_hi, b_hi, p));
                (out_lo, out_hi)
            };

            res[..4].copy_from_slice(&out_lo);
            res[4..].copy_from_slice(&out_hi);
        }
        _ => panic!("Currently unsupported width for packed addition"),
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
            // Perfectly fits into a uint32x4_t vector.
            let out: [u32; 4] = unsafe {
                let a = array_to_uint32x4([a[0], a[1], a[2], a[3]]);
                let b = array_to_uint32x4([b[0], b[1], b[2], b[3]]);
                let p: uint32x4_t = aarch64::vdupq_n_u32(p);
                uint32x4_to_array(uint32x4_mod_sub(a, b, p))
            };

            res.copy_from_slice(&out);
        }
        5 => {
            // We fit what we can into a uint32x4_t element.
            // The final sub is done using a scalar subtraction.
            let out: [u32; 4] = unsafe {
                let a = array_to_uint32x4([a[0], a[1], a[2], a[3]]);
                let b = array_to_uint32x4([b[0], b[1], b[2], b[3]]);
                let p: uint32x4_t = aarch64::vdupq_n_u32(p);
                uint32x4_to_array(uint32x4_mod_sub(a, b, p))
            };

            res[4] = scalar_sub(a[4], b[4]);

            res[..4].copy_from_slice(&out);
        }
        8 => {
            // This perfectly fits into two uint32x4_t elements.
            let (out_lo, out_hi): ([u32; 4], [u32; 4]) = unsafe {
                let p: uint32x4_t = aarch64::vdupq_n_u32(p);

                let a_lo = array_to_uint32x4([a[0], a[1], a[2], a[3]]);
                let b_lo = array_to_uint32x4([b[0], b[1], b[2], b[3]]);
                let out_lo = uint32x4_to_array(uint32x4_mod_sub(a_lo, b_lo, p));

                let a_hi = array_to_uint32x4([a[4], a[5], a[6], a[7]]);
                let b_hi = array_to_uint32x4([b[4], b[5], b[6], b[7]]);
                let out_hi = uint32x4_to_array(uint32x4_mod_sub(a_hi, b_hi, p));
                (out_lo, out_hi)
            };

            res[..4].copy_from_slice(&out_lo);
            res[4..].copy_from_slice(&out_hi);
        }
        _ => panic!("Currently unsupported width for packed subtraction"),
    }
}
