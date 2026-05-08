// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! Scalar Poseidon1 permutation at width 8 for Goldilocks.
//!
//! Parameters:
//! - S-box `x^7` (smallest `d` with `gcd(d, p - 1) = 1` for Goldilocks)
//! - `R_F = 8` full rounds (4 initial + 4 terminal)
//! - `R_P = 22` partial rounds in the middle
//! - External MDS is the circulant matrix with first row `[2, -4, -2, 8, 1, 1, 4, 1]`
//!   (small signed coefficients — multiplications strength-reduce to shifts and adds).
//!
//! The permutation is generic over any algebra `R` over `Goldilocks` that also
//! implements `InjectiveMonomial<7>`, mirroring the koala-bear crate's
//! Poseidon1 surface.

use std::sync::OnceLock;

#[cfg(any(
    test,
    not(any(
        all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")),
        all(target_arch = "x86_64", target_feature = "avx512f"),
    )),
))]
use field::PackedValue;
use field::{Algebra, Field, InjectiveMonomial, PrimeCharacteristicRing};

use crate::Goldilocks;

pub const POSEIDON1_WIDTH: usize = 8;
pub const POSEIDON1_HALF_FULL_ROUNDS: usize = 4;
pub const POSEIDON1_PARTIAL_ROUNDS: usize = 22;
pub const POSEIDON1_SBOX_DEGREE: u64 = 7;
pub const POSEIDON1_DIGEST_LEN: usize = 4;

pub const POSEIDON1_N_ROUNDS: usize = 2 * POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS;

// =========================================================================
// MDS matrix (circulant, width 8)
// =========================================================================
//
// First row of the circulant MDS matrix. Coefficients are small signed
// integers in `{-4, -2, 1, 2, 4, 8}` so each `c * s` strength-reduces to a
// shift (and a negation for `c < 0`) instead of a full multiply.
// `M[i][j] = MDS8_ROW[(j - i) mod 8]`.
pub const MDS8_ROW: [i64; 8] = [2, -4, -2, 8, 1, 1, 4, 1];

/// Convert a signed MDS coefficient to a `Goldilocks` element.
#[inline(always)]
const fn mds_coeff_as_goldilocks(c: i64) -> Goldilocks {
    if c >= 0 {
        Goldilocks::new(c as u64)
    } else {
        // -c fits in u64 since |c| <= 8.
        Goldilocks::new(crate::P.wrapping_sub((-c) as u64))
    }
}

/// Apply the width-8 circulant MDS matrix in place, generic over `R`.
///
/// The matrix has tiny integer entries (`|c| <= 8`), so even without any
/// delayed reduction a plain algebra-over-Goldilocks multiply is fine.
#[inline]
fn mds_mul_generic<R: Algebra<Goldilocks>>(state: &mut [R; 8]) {
    // Precompute the constants as Goldilocks once — `From<Goldilocks>` for `R`
    // gives us `R` conversions.
    let coeffs: [Goldilocks; 8] = {
        let mut arr = [Goldilocks::ZERO; 8];
        let mut i = 0;
        while i < 8 {
            arr[i] = mds_coeff_as_goldilocks(MDS8_ROW[i]);
            i += 1;
        }
        arr
    };

    let input = *state;
    for i in 0..8 {
        // `row_i · input = sum_j ROW[(j - i) mod 8] · input[j]`
        let mut acc = input[0] * coeffs[(8 - i) % 8];
        for j in 1..8 {
            acc += input[j] * coeffs[(j + 8 - i) % 8];
        }
        state[i] = acc;
    }
}

// BIAS_LL + (BIAS_HL << 32) = 8 * P. Each accumulator is biased so that the
// negative contributions never underflow u64. Each bias also exceeds the
// largest negative partial-sum (6 * (2^32 - 1) ≈ 2^34.6), so neither lane
// underflows during accumulation regardless of order.
const MDS_BIAS_LL: u64 = 0x0000_0007_0000_0008;
const MDS_BIAS_HL: u64 = 0x0000_0007_FFFF_FFF1;

/// Apply one MDS row coefficient `c ∈ {-4,-2,1,2,4,8}` for column `j`. The
/// const generic `C` lets each call site specialize: `c * s` collapses to a
/// shift (and a sign flip for negative `c`).
#[inline(always)]
fn mds_accum_term<const C: i64>(ll: &mut u64, hl: &mut u64, s_lo: u64, s_hi: u64) {
    match C {
        1 => {
            *ll = ll.wrapping_add(s_lo);
            *hl = hl.wrapping_add(s_hi);
        }
        2 => {
            *ll = ll.wrapping_add(s_lo << 1);
            *hl = hl.wrapping_add(s_hi << 1);
        }
        4 => {
            *ll = ll.wrapping_add(s_lo << 2);
            *hl = hl.wrapping_add(s_hi << 2);
        }
        8 => {
            *ll = ll.wrapping_add(s_lo << 3);
            *hl = hl.wrapping_add(s_hi << 3);
        }
        -2 => {
            *ll = ll.wrapping_sub(s_lo << 1);
            *hl = hl.wrapping_sub(s_hi << 1);
        }
        -4 => {
            *ll = ll.wrapping_sub(s_lo << 2);
            *hl = hl.wrapping_sub(s_hi << 2);
        }
        _ => panic!("unsupported MDS coefficient"),
    }
}

/// Accumulate one full row `[c0..c7]` (a circular shift of `MDS8_ROW`),
/// compose into a `u128` and reduce. Each `mds_accum_term::<Ck>` is
/// monomorphised so the row reduces to a straight-line sequence of
/// shift / add / sub instructions — no runtime branches, no `i128` carries.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn mds_row_scalar<
    const C0: i64,
    const C1: i64,
    const C2: i64,
    const C3: i64,
    const C4: i64,
    const C5: i64,
    const C6: i64,
    const C7: i64,
>(
    s_lo: &[u64; 8],
    s_hi: &[u64; 8],
) -> Goldilocks {
    let mut ll: u64 = MDS_BIAS_LL;
    let mut hl: u64 = MDS_BIAS_HL;
    mds_accum_term::<C0>(&mut ll, &mut hl, s_lo[0], s_hi[0]);
    mds_accum_term::<C1>(&mut ll, &mut hl, s_lo[1], s_hi[1]);
    mds_accum_term::<C2>(&mut ll, &mut hl, s_lo[2], s_hi[2]);
    mds_accum_term::<C3>(&mut ll, &mut hl, s_lo[3], s_hi[3]);
    mds_accum_term::<C4>(&mut ll, &mut hl, s_lo[4], s_hi[4]);
    mds_accum_term::<C5>(&mut ll, &mut hl, s_lo[5], s_hi[5]);
    mds_accum_term::<C6>(&mut ll, &mut hl, s_lo[6], s_hi[6]);
    mds_accum_term::<C7>(&mut ll, &mut hl, s_lo[7], s_hi[7]);

    // Compose `(hl << 32) + ll` into a u128 (hi, lo) pair.
    let hl_shifted = hl << 32;
    let (lo, carry) = ll.overflowing_add(hl_shifted);
    let hi = (hl >> 32).wrapping_add(carry as u64);
    crate::goldilocks::reduce128(((hi as u128) << 64) | (lo as u128))
}

/// Specialized fast MDS for the concrete `Goldilocks` scalar.
///
/// Each output is a dot product `sum_j MDS_ROW[(j-i) mod 8] * state[j]` with
/// signed MDS coefficients in `{-4, -2, 1, 2, 4, 8}`. We split each state
/// element into low/high 32-bit halves and accumulate `c * s_lo` / `c * s_hi`
/// separately into u64 lanes (no `i128` carry chains). Each `c * s_*` is a
/// `shl` (and a sign flip for negative `c`); 8 such terms per output stay in
/// u36 even with the bias, then a single compose+`reduce128` produces the
/// final element. Mirrors the AVX2/AVX512 packed paths' bias scheme.
#[inline(always)]
fn mds_mul_scalar(state: &mut [Goldilocks; 8]) {
    // Sanity: the row decomposition below assumes the canonical
    // [2, -4, -2, 8, 1, 1, 4, 1] coefficient set.
    const _: () = assert!(MDS8_ROW[0] == 2);
    const _: () = assert!(MDS8_ROW[1] == -4);
    const _: () = assert!(MDS8_ROW[2] == -2);
    const _: () = assert!(MDS8_ROW[3] == 8);
    const _: () = assert!(MDS8_ROW[4] == 1);
    const _: () = assert!(MDS8_ROW[5] == 1);
    const _: () = assert!(MDS8_ROW[6] == 4);
    const _: () = assert!(MDS8_ROW[7] == 1);

    // Pre-split each lane into low/high 32-bit halves. Both halves are u32,
    // so `c * s_*` (with `|c| <= 8`) fits in u35 and an 8-term row sum stays
    // in u38, comfortably within u64 even after biasing.
    let s_lo: [u64; 8] = core::array::from_fn(|i| state[i].value & 0xFFFF_FFFF);
    let s_hi: [u64; 8] = core::array::from_fn(|i| state[i].value >> 32);

    // Row i = MDS_ROW rotated right by i.
    state[0] = mds_row_scalar::<2, -4, -2, 8, 1, 1, 4, 1>(&s_lo, &s_hi);
    state[1] = mds_row_scalar::<1, 2, -4, -2, 8, 1, 1, 4>(&s_lo, &s_hi);
    state[2] = mds_row_scalar::<4, 1, 2, -4, -2, 8, 1, 1>(&s_lo, &s_hi);
    state[3] = mds_row_scalar::<1, 4, 1, 2, -4, -2, 8, 1>(&s_lo, &s_hi);
    state[4] = mds_row_scalar::<1, 1, 4, 1, 2, -4, -2, 8>(&s_lo, &s_hi);
    state[5] = mds_row_scalar::<8, 1, 1, 4, 1, 2, -4, -2>(&s_lo, &s_hi);
    state[6] = mds_row_scalar::<-2, 8, 1, 1, 4, 1, 2, -4>(&s_lo, &s_hi);
    state[7] = mds_row_scalar::<-4, -2, 8, 1, 1, 4, 1, 2>(&s_lo, &s_hi);
}

// =========================================================================
// Round constants (width 8)
// =========================================================================
//
// Layout: [4 initial full][22 partial][4 terminal full].
// Generated by the Grain LFSR (Poseidon1, Appendix E) with
// `field_type = 1, alpha = 7, n = 64, t = 8, R_F = 8, R_P = 22`.
// Values carried over verbatim from `plonky3/goldilocks/src/poseidon1.rs`.
pub const GOLDILOCKS_POSEIDON1_RC_8: [[Goldilocks; POSEIDON1_WIDTH]; POSEIDON1_N_ROUNDS] = Goldilocks::new_2d_array([
    // ---- Initial full rounds (4) ----
    [
        0xdd5743e7f2a5a5d9,
        0xcb3a864e58ada44b,
        0xffa2449ed32f8cdc,
        0x42025f65d6bd13ee,
        0x7889175e25506323,
        0x34b98bb03d24b737,
        0xbdcc535ecc4faa2a,
        0x5b20ad869fc0d033,
    ],
    [
        0xf1dda5b9259dfcb4,
        0x27515210be112d59,
        0x4227d1718c766c3f,
        0x26d333161a5bd794,
        0x49b938957bf4b026,
        0x4a56b5938b213669,
        0x1120426b48c8353d,
        0x6b323c3f10a56cad,
    ],
    [
        0xce57d6245ddca6b2,
        0xb1fc8d402bba1eb1,
        0xb5c5096ca959bd04,
        0x6db55cd306d31f7f,
        0xc49d293a81cb9641,
        0x1ce55a4fe979719f,
        0xa92e60a9d178a4d1,
        0x002cc64973bcfd8c,
    ],
    [
        0xcea721cce82fb11b,
        0xe5b55eb8098ece81,
        0x4e30525c6f1ddd66,
        0x43c6702827070987,
        0xaca68430a7b5762a,
        0x3674238634df9c93,
        0x88cee1c825e33433,
        0xde99ae8d74b57176,
    ],
    // ---- Partial rounds (22) ----
    [
        0x488897d85ff51f56,
        0x1140737ccb162218,
        0xa7eeb9215866ed35,
        0x9bd2976fee49fcc9,
        0xc0c8f0de580a3fcc,
        0x4fb2dae6ee8fc793,
        0x343a89f35f37395b,
        0x223b525a77ca72c8,
    ],
    [
        0x56ccb62574aaa918,
        0xc4d507d8027af9ed,
        0xa080673cf0b7e95c,
        0xf0184884eb70dcf8,
        0x044f10b0cb3d5c69,
        0xe9e3f7993938f186,
        0x1b761c80e772f459,
        0x606cec607a1b5fac,
    ],
    [
        0x14a0c2e1d45f03cd,
        0x4eace8855398574f,
        0xf905ca7103eff3e6,
        0xf8c8f8d20862c059,
        0xb524fe8bdd678e5a,
        0xfbb7865901a1ec41,
        0x014ef1197d341346,
        0x9725e20825d07394,
    ],
    [
        0xfdb25aef2c5bae3b,
        0xbe5402dc598c971e,
        0x93a5711f04cdca3d,
        0xc45a9a5b2f8fb97b,
        0xfe8946a924933545,
        0x2af997a27369091c,
        0xaa62c88e0b294011,
        0x058eb9d810ce9f74,
    ],
    [
        0xb3cb23eced349ae4,
        0xa3648177a77b4a84,
        0x43153d905992d95d,
        0xf4e2a97cda44aa4b,
        0x5baa2702b908682f,
        0x082923bdf4f750d1,
        0x98ae09a325893803,
        0xf8a6475077968838,
    ],
    [
        0xceb0735bf00b2c5f,
        0x0a1a5d953888e072,
        0x2fcb190489f94475,
        0xb5be06270dec69fc,
        0x739cb934b09acf8b,
        0x537750b75ec7f25b,
        0xe9dd318bae1f3961,
        0xf7462137299efe1a,
    ],
    [
        0xb1f6b8eee9adb940,
        0xbdebcc8a809dfe6b,
        0x40fc1f791b178113,
        0x3ac1c3362d014864,
        0x9a016184bdb8aeba,
        0x95f2394459fbc25e,
        0xe3f34a07a76a66c2,
        0x8df25f9ad98b1b96,
    ],
    [
        0x85ffc27171439d9d,
        0xddcb9a2dcfd26910,
        0x26b5ba4bf3afb94e,
        0xffff9cc7c7651e2f,
        0x8c88364698280b55,
        0xebc114167b910501,
        0x2d77b4d89ecfb516,
        0x332e0828eba151f2,
    ],
    [
        0x46fa6a6450dd4735,
        0xd00db7dd92384a33,
        0x5fd4fb751f3a5fc5,
        0x496fb90c0bb65ea2,
        0xf3baec0bb87cc5c7,
        0x862a3c0a7d4c7713,
        0xbf5f38336a3f47d8,
        0x41ad9dbc1394a20c,
    ],
    [
        0xcc535945b7dbf0f7,
        0x82af2bc93685bcec,
        0x8e4c8d0c8cebfccd,
        0x17cb39417e84597e,
        0xd4a965a8c749b232,
        0xa2cab040f33f3ee5,
        0xa98811a1fed4e3a6,
        0x1cc48b54f377e2a1,
    ],
    [
        0xe40cd4f6c5609a27,
        0x11de79ebca97a4a4,
        0x9177c73d8b7e929d,
        0x2a6fe8085797e792,
        0x3de6e93329f8d5ae,
        0x3f7af9125da962ff,
        0xd710682cfc77d3ac,
        0x48faf05f3b053cf4,
    ],
    [
        0x287db8630da89c8b,
        0x4d0de32053cb30e9,
        0x8b37a4f20c5ada7b,
        0xe7cc6ebe78c84ecf,
        0x240bdc0a66a2610d,
        0x8299e7f02caa1650,
        0x380a53fefb6e754e,
        0x684a1d8cf8eb6810,
    ],
    [
        0xe839452eb4b8a5e1,
        0xb03fa62e90626af4,
        0x11a688602fbc5efc,
        0x30dda75c355a2d62,
        0x0f712adcb73810de,
        0xffdc1102187f1ae1,
        0x40c34f398254b99c,
        0xede021b9dc289a4a,
    ],
    [
        0x8b7b05225c4e7dad,
        0x3bc794346f9d9ff9,
        0xfccb5a57f2ca86ff,
        0xbb1502015a7da9d4,
        0xd7e0a35d4352a015,
        0x27af7a44f8160931,
        0xc37442f6782f4615,
        0xbdf392a9bd095dcb,
    ],
    [
        0xc17f55037cf00de9,
        0xbcffedd34c71a874,
        0x5eb45d2a8133d1f2,
        0xbabe251e1612ebdf,
        0x3efeb9fbe438c536,
        0x2d7cef97b4afe1cf,
        0xe5de1b4660016c0b,
        0xcdcc26c332f5657c,
    ],
    [
        0xe01dd653daf15809,
        0xb0a6bdd4b41094b5,
        0x27eac858b0b03a05,
        0x51d43b5e93adbdc0,
        0x8b89a23b0fea5fc9,
        0xdc8ac3b14f7f2fc1,
        0xe793f82f1efec039,
        0x9f6f2cf8969e7b80,
    ],
    [
        0x49d45382e0f21d4a,
        0x5f4ad1797cd72786,
        0x4dc3dbebfd45f795,
        0x03a3ef84dba6e1bc,
        0x204bc9b3d3fc4c01,
        0x9ad706081e89b9ba,
        0x638bfb4d840e9f89,
        0x5ef2938cd095ae35,
    ],
    [
        0x42cca18ebeb265c8,
        0xb7b2ec5c29aecbf8,
        0x0d84f9535dc78f0f,
        0x04e64ad942e77b8c,
        0xb4880dffffc9da0b,
        0x16db16d9c29adeb1,
        0x09bbaf2a0590cd1e,
        0x76460e74961fcf8d,
    ],
    [
        0xed12a2276dfa1553,
        0x0b5acec5de0436fd,
        0x3c6cfea033a1f0a8,
        0x2b5ecefe546cac15,
        0x6e2d82884cd3bf6f,
        0xc134878d1add7b83,
        0x997963422eb7a280,
        0x5e834537ac648cf6,
    ],
    [
        0x89e779214737c0b7,
        0x1a8c05e8581ad95b,
        0x8d18b72796437cf7,
        0xe7252c949e04b106,
        0x53267c4fd174585a,
        0xa16ef5d9c81dad47,
        0xda65191937270a46,
        0xcb2a5b55f2df664c,
    ],
    [
        0x854aee2dc1924137,
        0xf37013c9d479ece6,
        0x0e163bc0630c4696,
        0x384ee64955048f76,
        0xf65d814e28ee4ec5,
        0xe57bc564fd82f1b1,
        0x4b338937b6876614,
        0x66ee0b04ed43cd8d,
    ],
    [
        0x49884bf25f4ef15d,
        0xeb51fe28de1c6f54,
        0x2cd64e84fce8dfcc,
        0x29164a96a541a013,
        0x173ce7558f4cacb8,
        0xeb5b1ce5877c89e9,
        0x5faff4b0f5217bf6,
        0xac42d0b1c20f205e,
    ],
    // ---- Terminal full rounds (4) ----
    [
        0xfb1d6bf0ca43221b,
        0x97b0a1b01d6a2955,
        0x08c60bd622952b30,
        0x43f2be0f9e24147c,
        0xfa7268b7d3730f5d,
        0x43a6c419a23983bb,
        0xcd77c1f7b29b113c,
        0xcfa43c9db8eec29f,
    ],
    [
        0xcaaa95a6c7365dec,
        0x0a91193f798f3be0,
        0x1104497652735dc6,
        0x35aecb93663b515e,
        0x8dbc9916065aa858,
        0xada8f7a0266579ed,
        0x524dee7bec1ea789,
        0xa93aee9dd5af9521,
    ],
    [
        0x9d1f1b54750d707e,
        0x7c9feab87096d5dc,
        0xa2e1fb19f9d4261b,
        0xb714deb448de6346,
        0x225d1f0d011c5403,
        0x1549b7f1d28cedc0,
        0xaef3e46f97d43942,
        0x6dfc7ffe0b38bf08,
    ],
    [
        0x7de853fdc542b663,
        0xa68ecc96610657b2,
        0xe88bb5428af289b1,
        0xd7cfa1504c5569f5,
        0x78a9aad0d642d30a,
        0xd68315f2353dce52,
        0x46e56300f86fcfd5,
        0x323d95332b145fd6,
    ],
]);

// =========================================================================
// Round-constant compression for partial rounds
// =========================================================================
//
// In the original spec each partial round is
//   state += rc[r]; state[0] = sbox(state[0]); state = MDS * state.
// By linearity, the rc[r][1..7] components of every partial RC can be
// commuted forward through the linear (MDS) layers and accumulated into
// 1) a single per-round scalar `α_r` added to `state[0]` before its sbox,
// 2) a residual vector `δ` absorbed into the first terminal-full-round RC.
//
// Per partial round this saves 7 of the 8 RC adds (≈146 fewer adds per
// compression). Crucially the MDS layer is unchanged — we still call the
// existing cheap shift-MDS (`mds_mul_scalar` / `mds_mul_simd`), so the small
// `{-4,-2,1,2,4,8}` coefficients keep paying off.
//
// Recurrence (forward, starting from δ_{-1} = 0):
//   α_r        = δ_{r-1}[0] + rc[r][0]
//   e_r        = (0, δ_{r-1}[1] + rc[r][1], …, δ_{r-1}[7] + rc[r][7])
//   δ_r        = MDS · e_r
// The accumulated δ_{RP-1} is added to the original first terminal RC to
// give `terminal_rc0_adjusted`. The optimization is mathematically
// equivalent — the captured `test_known_answer` output is unchanged.

fn mds_matrix() -> [[Goldilocks; 8]; 8] {
    let mut m = [[Goldilocks::ZERO; 8]; 8];
    for i in 0..8 {
        for j in 0..8 {
            m[i][j] = mds_coeff_as_goldilocks(MDS8_ROW[(j + 8 - i) % 8]);
        }
    }
    m
}

fn mds_apply(m: &[[Goldilocks; 8]; 8], v: &[Goldilocks; 8]) -> [Goldilocks; 8] {
    core::array::from_fn(|i| {
        let mut s = Goldilocks::ZERO;
        for j in 0..8 {
            s += m[i][j] * v[j];
        }
        s
    })
}

#[derive(Debug)]
struct Precomputed {
    /// Per-round scalar RC added to `state[0]` before its sbox. Length = RP.
    alphas: [Goldilocks; POSEIDON1_PARTIAL_ROUNDS],
    /// First terminal-full-round RC, with the RP-residual `δ_{RP-1}` baked in.
    terminal_rc0_adjusted: [Goldilocks; 8],
}

fn precomputed() -> &'static Precomputed {
    static PRECOMPUTED: OnceLock<Precomputed> = OnceLock::new();
    PRECOMPUTED.get_or_init(|| {
        let mds = mds_matrix();

        let mut alphas = [Goldilocks::ZERO; POSEIDON1_PARTIAL_ROUNDS];
        let mut delta = [Goldilocks::ZERO; 8];

        for r in 0..POSEIDON1_PARTIAL_ROUNDS {
            let rc = &GOLDILOCKS_POSEIDON1_RC_8[POSEIDON1_HALF_FULL_ROUNDS + r];
            // α_r absorbs the [0]-component of the residual + this round's rc[r][0].
            alphas[r] = delta[0] + rc[0];
            // Form e_r = (0, δ[1..] + rc[1..]). The [0] slot is zero so the
            // sbox commutes past it (sbox is identity on indices ≥ 1).
            let mut e = [Goldilocks::ZERO; 8];
            for i in 1..8 {
                e[i] = delta[i] + rc[i];
            }
            // δ_r = MDS · e_r, ready for next iteration.
            delta = mds_apply(&mds, &e);
        }

        // Absorb δ_{RP-1} into the first terminal-full-round RC so the
        // optimized partial block transitions cleanly into the original
        // terminal-round code.
        let terminal_rc0 = &GOLDILOCKS_POSEIDON1_RC_8[POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS];
        let mut terminal_rc0_adjusted = [Goldilocks::ZERO; 8];
        for i in 0..8 {
            terminal_rc0_adjusted[i] = terminal_rc0[i] + delta[i];
        }

        Precomputed {
            alphas,
            terminal_rc0_adjusted,
        }
    })
}

// =========================================================================
// S-box helpers
// =========================================================================

#[inline(always)]
fn sbox_full<R: InjectiveMonomial<7>>(x: R) -> R {
    x.injective_exp_n()
}

// =========================================================================
// Permutation driver
// =========================================================================

/// Width-8 Poseidon1 permutation for Goldilocks.
///
/// Zero-sized — all state lives in the round-constant tables above. Mirrors
/// `Poseidon1Goldilocks8`'s public surface: `permute{,_mut}`,
/// `compress{,_in_place}`, plus a `default_goldilocks_poseidon1_8()` constructor.
#[derive(Clone, Copy, Debug, Default)]
pub struct Poseidon1Goldilocks8;

impl Poseidon1Goldilocks8 {
    /// Fast scalar permutation — direct `Goldilocks` arithmetic with a `u128`
    /// MDS accumulator.
    pub fn permute(&self, mut state: [Goldilocks; POSEIDON1_WIDTH]) -> [Goldilocks; POSEIDON1_WIDTH] {
        self.permute_mut(&mut state);
        state
    }

    #[inline]
    pub fn permute_mut(&self, state: &mut [Goldilocks; POSEIDON1_WIDTH]) {
        let pre = precomputed();

        // Initial full rounds.
        for rc in GOLDILOCKS_POSEIDON1_RC_8.iter().take(POSEIDON1_HALF_FULL_ROUNDS) {
            for (i, s) in state.iter_mut().enumerate() {
                *s += rc[i];
            }
            for s in state.iter_mut() {
                *s = sbox_full::<Goldilocks>(*s);
            }
            mds_mul_scalar(state);
        }

        // Partial rounds with compressed RCs: only state[0] gets a (precomputed)
        // scalar RC each round; the other 7 components' contributions live in
        // `terminal_rc0_adjusted` and are absorbed at the first terminal round.
        for r in 0..POSEIDON1_PARTIAL_ROUNDS {
            state[0] += pre.alphas[r];
            state[0] = sbox_full::<Goldilocks>(state[0]);
            mds_mul_scalar(state);
        }

        // Terminal full rounds; first round uses the residual-adjusted RC.
        for (k, rc) in GOLDILOCKS_POSEIDON1_RC_8
            .iter()
            .take(POSEIDON1_N_ROUNDS)
            .skip(POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS)
            .enumerate()
        {
            let rc_eff = if k == 0 { &pre.terminal_rc0_adjusted } else { rc };
            for (i, s) in state.iter_mut().enumerate() {
                *s += rc_eff[i];
            }
            for s in state.iter_mut() {
                *s = sbox_full::<Goldilocks>(*s);
            }
            mds_mul_scalar(state);
        }
    }

    /// Generic permutation over any algebra `R` over `Goldilocks` with `x^7`
    /// as an injective monomial. Used by the AIR / symbolic trace builders.
    pub fn permute_generic<R>(&self, state: &mut [R; POSEIDON1_WIDTH])
    where
        R: Algebra<Goldilocks> + InjectiveMonomial<7> + Copy,
    {
        for rc in GOLDILOCKS_POSEIDON1_RC_8.iter().take(POSEIDON1_HALF_FULL_ROUNDS) {
            for (i, s) in state.iter_mut().enumerate() {
                *s += rc[i];
            }
            for s in state.iter_mut() {
                *s = sbox_full::<R>(*s);
            }
            mds_mul_generic(state);
        }

        for rc in GOLDILOCKS_POSEIDON1_RC_8
            .iter()
            .skip(POSEIDON1_HALF_FULL_ROUNDS)
            .take(POSEIDON1_PARTIAL_ROUNDS)
        {
            for (i, s) in state.iter_mut().enumerate() {
                *s += rc[i];
            }
            state[0] = sbox_full::<R>(state[0]);
            mds_mul_generic(state);
        }

        for rc in GOLDILOCKS_POSEIDON1_RC_8
            .iter()
            .take(POSEIDON1_N_ROUNDS)
            .skip(POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS)
        {
            for (i, s) in state.iter_mut().enumerate() {
                *s += rc[i];
            }
            for s in state.iter_mut() {
                *s = sbox_full::<R>(*s);
            }
            mds_mul_generic(state);
        }
    }

    /// Compression-mode in-place permutation: `output = permute(input) + input`.
    ///
    /// When `R` matches the architecture's packed Goldilocks type, dispatches
    /// to the SIMD-parallel path. When `R == Goldilocks`, uses the scalar fast
    /// path (avoids the symbolic-friendly but slow `permute_generic`).
    /// Otherwise falls back to the generic algebra path.
    #[inline]
    pub fn compress_in_place<R>(&self, state: &mut [R; POSEIDON1_WIDTH])
    where
        R: Algebra<Goldilocks> + InjectiveMonomial<7> + Copy + 'static,
    {
        use core::any::TypeId;

        type Packing = <Goldilocks as Field>::Packing;

        if TypeId::of::<R>() == TypeId::of::<Packing>() {
            // SAFETY: TypeId equality guarantees R has the same layout as Packing,
            // and the array is repr-transparent as a slice of W*8 Goldilocks.
            let s = unsafe { &mut *(state as *mut [R; POSEIDON1_WIDTH] as *mut [Packing; POSEIDON1_WIDTH]) };
            self.compress_in_place_simd(s);
            return;
        }
        if TypeId::of::<R>() == TypeId::of::<Goldilocks>() {
            // SAFETY: TypeId equality.
            let s = unsafe { &mut *(state as *mut [R; POSEIDON1_WIDTH] as *mut [Goldilocks; POSEIDON1_WIDTH]) };
            let initial = *s;
            self.permute_mut(s);
            for (slot, init) in s.iter_mut().zip(initial) {
                *slot += init;
            }
            return;
        }

        let initial = *state;
        self.permute_generic(state);
        for (s, init) in state.iter_mut().zip(initial) {
            *s += init;
        }
    }

    /// SIMD-parallel compression over `<Goldilocks as Field>::Packing`.
    ///
    /// On x86_64 (AVX2 or AVX512), keeps state in packed registers throughout
    /// the rounds. RC adds and sboxes use the packed `Add`/`square`/`Mul`
    /// (which fully reduce), and the MDS uses the dedicated `mds_mul_simd`
    /// (delayed reduction via shift+add multiplication by tiny constants).
    ///
    /// On other architectures (e.g. aarch64+NEON, scalar fallback), we
    /// deinterleave to per-lane scalar arrays and run the rounds in lockstep
    /// across all W lanes. The scalar `mds_mul_scalar` (u64 lo/hi-32 split +
    /// single `reduce128` per output) is far cheaper than the packed type's
    /// fully-reducing `Mul`. A NEON-vectorized `mds_mul_simd` was tried and
    /// regressed on Apple Silicon: keeping state in `uint64x2_t` would force
    /// per-element NEON↔GPR shuffles around the (faster scalar) RC adds and
    /// sboxes, eating the MDS win.
    #[inline]
    fn compress_in_place_simd(&self, state: &mut [<Goldilocks as Field>::Packing; POSEIDON1_WIDTH]) {
        #[cfg(any(
            all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")),
            all(target_arch = "x86_64", target_feature = "avx512f"),
        ))]
        {
            type P = <Goldilocks as Field>::Packing;

            #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
            use crate::x86_64_avx2::packing::mds_mul_simd;
            #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
            use crate::x86_64_avx512::packing::mds_mul_simd;

            let pre = precomputed();
            let initial = *state;

            // Initial full rounds.
            for rc in GOLDILOCKS_POSEIDON1_RC_8.iter().take(POSEIDON1_HALF_FULL_ROUNDS) {
                for (i, s) in state.iter_mut().enumerate() {
                    *s += P::from(rc[i]);
                }
                for s in state.iter_mut() {
                    *s = sbox_full::<P>(*s);
                }
                mds_mul_simd(state);
            }

            // Partial rounds with compressed RCs.
            for r in 0..POSEIDON1_PARTIAL_ROUNDS {
                state[0] += P::from(pre.alphas[r]);
                state[0] = sbox_full::<P>(state[0]);
                mds_mul_simd(state);
            }

            // Terminal full rounds; first round uses the residual-adjusted RC.
            for (k, rc) in GOLDILOCKS_POSEIDON1_RC_8
                .iter()
                .take(POSEIDON1_N_ROUNDS)
                .skip(POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS)
                .enumerate()
            {
                let rc_eff = if k == 0 { &pre.terminal_rc0_adjusted } else { rc };
                for (i, s) in state.iter_mut().enumerate() {
                    *s += P::from(rc_eff[i]);
                }
                for s in state.iter_mut() {
                    *s = sbox_full::<P>(*s);
                }
                mds_mul_simd(state);
            }

            // Compression-mode add-back of the original input.
            for (s, init) in state.iter_mut().zip(initial) {
                *s += init;
            }
        }

        #[cfg(not(any(
            all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")),
            all(target_arch = "x86_64", target_feature = "avx512f"),
        )))]
        {
            type P = <Goldilocks as Field>::Packing;
            const W: usize = <P as PackedValue>::WIDTH;

            let mut lanes: [[Goldilocks; POSEIDON1_WIDTH]; W] = [[Goldilocks::ZERO; POSEIDON1_WIDTH]; W];
            for i in 0..POSEIDON1_WIDTH {
                let s = state[i].as_slice();
                for (k, lane) in lanes.iter_mut().enumerate() {
                    lane[i] = s[k];
                }
            }
            let initial = lanes;

            // Initial full rounds.
            for rc in GOLDILOCKS_POSEIDON1_RC_8.iter().take(POSEIDON1_HALF_FULL_ROUNDS) {
                for lane in lanes.iter_mut() {
                    for (i, s) in lane.iter_mut().enumerate() {
                        *s += rc[i];
                    }
                }
                for lane in lanes.iter_mut() {
                    for s in lane.iter_mut() {
                        *s = sbox_full::<Goldilocks>(*s);
                    }
                }
                for lane in lanes.iter_mut() {
                    mds_mul_scalar(lane);
                }
            }

            let pre = precomputed();

            // Partial rounds with compressed RCs (per lane).
            for r in 0..POSEIDON1_PARTIAL_ROUNDS {
                let alpha = pre.alphas[r];
                for lane in lanes.iter_mut() {
                    lane[0] += alpha;
                    lane[0] = sbox_full::<Goldilocks>(lane[0]);
                }
                for lane in lanes.iter_mut() {
                    mds_mul_scalar(lane);
                }
            }

            // Terminal full rounds; first round uses residual-adjusted RC.
            for (k, rc) in GOLDILOCKS_POSEIDON1_RC_8
                .iter()
                .take(POSEIDON1_N_ROUNDS)
                .skip(POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS)
                .enumerate()
            {
                let rc_eff = if k == 0 { &pre.terminal_rc0_adjusted } else { rc };
                for lane in lanes.iter_mut() {
                    for (i, s) in lane.iter_mut().enumerate() {
                        *s += rc_eff[i];
                    }
                }
                for lane in lanes.iter_mut() {
                    for s in lane.iter_mut() {
                        *s = sbox_full::<Goldilocks>(*s);
                    }
                }
                for lane in lanes.iter_mut() {
                    mds_mul_scalar(lane);
                }
            }

            for i in 0..POSEIDON1_WIDTH {
                state[i] = P::from_fn(|k| lanes[k][i] + initial[k][i]);
            }
        }
    }
}

/// Return the default width-8 Poseidon1 permutation.
#[inline]
pub fn default_goldilocks_poseidon1_8() -> Poseidon1Goldilocks8 {
    Poseidon1Goldilocks8
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
#[allow(clippy::needless_range_loop)]
mod tests {
    use super::*;

    /// The scalar and generic paths must agree on all inputs.
    #[test]
    fn scalar_matches_generic() {
        let p = Poseidon1Goldilocks8;
        let mut input = [Goldilocks::ZERO; 8];
        for i in 0..8 {
            input[i] = Goldilocks::new(0xdead_beef_0000_0001u64.wrapping_mul(i as u64 + 1));
        }
        let fast = p.permute(input);
        let mut slow = input;
        p.permute_generic(&mut slow);
        assert_eq!(fast, slow);
    }

    /// SIMD MDS path must match the scalar MDS for arbitrary state.
    #[cfg(any(
        all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")),
        all(target_arch = "x86_64", target_feature = "avx512f"),
    ))]
    #[test]
    fn simd_mds_matches_scalar_mds() {
        type P = <Goldilocks as Field>::Packing;
        let width = <P as PackedValue>::WIDTH;

        // Build packed state with distinct per-lane values, including some
        // u64s near the field-order boundary to stress the reduction.
        let mut packed: [P; 8] = [P::ZERO; 8];
        let edges: [u64; 4] = [0, 1, crate::P - 1, u64::MAX];
        for i in 0..8 {
            packed[i] = P::from_fn(|k| {
                if k < 4 && i % 2 == 0 {
                    Goldilocks::new(edges[k])
                } else {
                    Goldilocks::new(0xa5a5_0000_0000_0001u64.wrapping_mul((i * 17 + k * 31 + 1) as u64))
                }
            });
        }
        let initial = packed;

        // Reference: per-lane scalar MDS.
        let mut expected_lanes: Vec<[Goldilocks; 8]> = (0..width)
            .map(|k| std::array::from_fn(|i| initial[i].as_slice()[k]))
            .collect();
        for lane in expected_lanes.iter_mut() {
            mds_mul_scalar(lane);
        }

        #[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
        crate::x86_64_avx2::packing::mds_mul_simd(&mut packed);
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
        crate::x86_64_avx512::packing::mds_mul_simd(&mut packed);

        for i in 0..8 {
            for k in 0..width {
                assert_eq!(
                    packed[i].as_slice()[k],
                    expected_lanes[k][i],
                    "mismatch at slot {i}, lane {k}"
                );
            }
        }
    }

    /// `compress_in_place::<Packing>` must agree with per-lane scalar compression.
    /// Exercises the SIMD dispatch branch.
    #[test]
    fn compress_in_place_dispatches_packed_correctly() {
        type P = <Goldilocks as Field>::Packing;
        let width = <P as PackedValue>::WIDTH;
        let p = Poseidon1Goldilocks8;

        // Build distinct inputs per lane so we'd notice a swap or duplication.
        let mut packed: [P; 8] = [P::ZERO; 8];
        for i in 0..8 {
            packed[i] =
                P::from_fn(|k| Goldilocks::new(0xa5a5_0000_0000_0001u64.wrapping_mul((i * 17 + k * 31 + 1) as u64)));
        }
        let initial = packed;

        // Reference: per-lane scalar compress.
        let mut expected_lanes: Vec<[Goldilocks; 8]> = (0..width)
            .map(|k| std::array::from_fn(|i| initial[i].as_slice()[k]))
            .collect();
        for lane in expected_lanes.iter_mut() {
            p.compress_in_place(lane);
        }

        p.compress_in_place(&mut packed);

        for i in 0..8 {
            for k in 0..width {
                assert_eq!(
                    packed[i].as_slice()[k],
                    expected_lanes[k][i],
                    "mismatch at slot {i}, lane {k}"
                );
            }
        }
    }

    /// The permutation is deterministic and non-trivial.
    #[test]
    fn permutation_is_deterministic() {
        let input: [Goldilocks; 8] = [
            Goldilocks::new(1),
            Goldilocks::new(2),
            Goldilocks::new(3),
            Goldilocks::new(4),
            Goldilocks::new(5),
            Goldilocks::new(6),
            Goldilocks::new(7),
            Goldilocks::new(8),
        ];
        let p = Poseidon1Goldilocks8;
        let a = p.permute(input);
        let b = p.permute(input);
        assert_eq!(a, b);
        assert_ne!(a, input);
    }

    /// Rough avalanche smoke test: distinct inputs produce distinct outputs.
    #[test]
    fn permutation_is_injective_on_small_inputs() {
        let p = Poseidon1Goldilocks8;
        let mut seen = std::collections::HashSet::new();
        for i in 0..64u64 {
            let mut input = [Goldilocks::ZERO; 8];
            input[0] = Goldilocks::new(i);
            let out = p.permute(input);
            assert!(seen.insert(out[0].value), "collision at i={i}");
        }
    }

    /// Known-answer regression test for the width-8 permutation under the
    /// custom signed-coefficient MDS `[2, -4, -2, 8, 1, 1, 4, 1]`. Output was
    /// captured from the scalar reference implementation; re-running the
    /// permutation must reproduce it bit-for-bit.
    #[test]
    fn test_known_answer() {
        use field::PrimeField64;

        let p = default_goldilocks_poseidon1_8();
        let mut input: [Goldilocks; 8] = [0, 1, 2, 3, 4, 5, 6, 7].map(Goldilocks::new);
        p.permute_mut(&mut input);
        let expected: [u64; 8] = [
            5090027972440212889,
            12553003895628898413,
            7769768437951802543,
            14813905934291611803,
            10867342912969274000,
            1190867883229247335,
            10567061940441997012,
            13814457048189538411,
        ];
        let got: [u64; 8] = input.map(|x| x.as_canonical_u64());
        assert_eq!(got, expected);
    }
}
