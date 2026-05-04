// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

//! Scalar Poseidon1 permutation at width 8 for Goldilocks.
//!
//! Parameters:
//! - S-box `x^7` (smallest `d` with `gcd(d, p - 1) = 1` for Goldilocks)
//! - `R_F = 8` full rounds (4 initial + 4 terminal)
//! - `R_P = 22` partial rounds in the middle
//! - External MDS is the circulant matrix with first row `[7, 1, 3, 8, 8, 3, 4, 9]`
//!   (Plonky2/upstream-Plonky3 "small MDS" — same matrix the upstream
//!   `MdsMatrixGoldilocks` uses at width 8).
//!
//! The permutation is generic over any algebra `R` over `Goldilocks` that also
//! implements `InjectiveMonomial<7>`, mirroring the koala-bear crate's
//! Poseidon1 surface.

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
// First row of the circulant MDS matrix. `MDS8_COL[i] = r_{(N - i) mod N}` is
// the first column — more convenient for a row-major apply of a circulant
// since `row_i = cyclic_shift(col, i)`, i.e. `M[i][j] = COL[(j - i + N) mod N]`
// (equivalently `ROW[(j - i) mod N]`).
pub const MDS8_ROW: [i64; 8] = [7, 1, 3, 8, 8, 3, 4, 9];

/// Apply the width-8 circulant MDS matrix in place, generic over `R`.
///
/// The matrix has tiny integer entries (max 9), so even without any delayed
/// reduction a plain algebra-over-Goldilocks multiply is fine.
#[inline]
fn mds_mul_generic<R: Algebra<Goldilocks>>(state: &mut [R; 8]) {
    // Precompute the constants as Goldilocks once — `From<Goldilocks>` for `R`
    // gives us `R` conversions.
    let coeffs: [Goldilocks; 8] = {
        let mut arr = [Goldilocks::ZERO; 8];
        for i in 0..8 {
            arr[i] = Goldilocks::new(MDS8_ROW[i] as u64);
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

/// Specialized fast MDS for the concrete `Goldilocks` scalar.
///
/// Each output is a dot product `sum_j MDS_ROW[(j-i) mod 8] * state[j]` with
/// MDS coefficients in `{1, 3, 4, 7, 8, 9}` (all fit in 4 bits). With the
/// constants spelled out explicitly LLVM strength-reduces `c * s` to shifts
/// and adds (e.g. `8*s = s<<3`, `7*s = (s<<3)-s`), eliminating the variable
/// multiplications entirely. We accumulate into `u128` (8·9·2^64 ≈ 2^71 fits
/// comfortably) and reduce once per output via `reduce128`. The explicit
/// `1 *` factors keep the circulant structure readable column-by-column.
#[inline(always)]
#[allow(clippy::identity_op)]
fn mds_mul_scalar(state: &mut [Goldilocks; 8]) {
    let s0 = state[0].value as u128;
    let s1 = state[1].value as u128;
    let s2 = state[2].value as u128;
    let s3 = state[3].value as u128;
    let s4 = state[4].value as u128;
    let s5 = state[5].value as u128;
    let s6 = state[6].value as u128;
    let s7 = state[7].value as u128;

    // MDS_ROW = [7, 1, 3, 8, 8, 3, 4, 9]; row i is MDS_ROW rotated right by i.
    let acc0 = 7 * s0 + 1 * s1 + 3 * s2 + 8 * s3 + 8 * s4 + 3 * s5 + 4 * s6 + 9 * s7;
    let acc1 = 9 * s0 + 7 * s1 + 1 * s2 + 3 * s3 + 8 * s4 + 8 * s5 + 3 * s6 + 4 * s7;
    let acc2 = 4 * s0 + 9 * s1 + 7 * s2 + 1 * s3 + 3 * s4 + 8 * s5 + 8 * s6 + 3 * s7;
    let acc3 = 3 * s0 + 4 * s1 + 9 * s2 + 7 * s3 + 1 * s4 + 3 * s5 + 8 * s6 + 8 * s7;
    let acc4 = 8 * s0 + 3 * s1 + 4 * s2 + 9 * s3 + 7 * s4 + 1 * s5 + 3 * s6 + 8 * s7;
    let acc5 = 8 * s0 + 8 * s1 + 3 * s2 + 4 * s3 + 9 * s4 + 7 * s5 + 1 * s6 + 3 * s7;
    let acc6 = 3 * s0 + 8 * s1 + 8 * s2 + 3 * s3 + 4 * s4 + 9 * s5 + 7 * s6 + 1 * s7;
    let acc7 = 1 * s0 + 3 * s1 + 8 * s2 + 8 * s3 + 3 * s4 + 4 * s5 + 9 * s6 + 7 * s7;

    state[0] = crate::goldilocks::reduce128(acc0);
    state[1] = crate::goldilocks::reduce128(acc1);
    state[2] = crate::goldilocks::reduce128(acc2);
    state[3] = crate::goldilocks::reduce128(acc3);
    state[4] = crate::goldilocks::reduce128(acc4);
    state[5] = crate::goldilocks::reduce128(acc5);
    state[6] = crate::goldilocks::reduce128(acc6);
    state[7] = crate::goldilocks::reduce128(acc7);
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
        for rc in GOLDILOCKS_POSEIDON1_RC_8.iter().take(POSEIDON1_HALF_FULL_ROUNDS) {
            for (i, s) in state.iter_mut().enumerate() {
                *s += rc[i];
            }
            for s in state.iter_mut() {
                *s = sbox_full::<Goldilocks>(*s);
            }
            mds_mul_scalar(state);
        }

        for rc in GOLDILOCKS_POSEIDON1_RC_8
            .iter()
            .skip(POSEIDON1_HALF_FULL_ROUNDS)
            .take(POSEIDON1_PARTIAL_ROUNDS)
        {
            for (i, s) in state.iter_mut().enumerate() {
                *s += rc[i];
            }
            state[0] = sbox_full::<Goldilocks>(state[0]);
            mds_mul_scalar(state);
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
    /// across all W lanes. The MDS coefficients are tiny (max 9), so the
    /// scalar `mds_mul_scalar` (u128 accumulator + single `reduce128` per
    /// output) is far cheaper than the packed type's fully-reducing `Mul`.
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

            // Partial rounds.
            for rc in GOLDILOCKS_POSEIDON1_RC_8
                .iter()
                .skip(POSEIDON1_HALF_FULL_ROUNDS)
                .take(POSEIDON1_PARTIAL_ROUNDS)
            {
                for (i, s) in state.iter_mut().enumerate() {
                    *s += P::from(rc[i]);
                }
                state[0] = sbox_full::<P>(state[0]);
                mds_mul_simd(state);
            }

            // Terminal full rounds.
            for rc in GOLDILOCKS_POSEIDON1_RC_8
                .iter()
                .take(POSEIDON1_N_ROUNDS)
                .skip(POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS)
            {
                for (i, s) in state.iter_mut().enumerate() {
                    *s += P::from(rc[i]);
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

            // Partial rounds.
            for rc in GOLDILOCKS_POSEIDON1_RC_8
                .iter()
                .skip(POSEIDON1_HALF_FULL_ROUNDS)
                .take(POSEIDON1_PARTIAL_ROUNDS)
            {
                for lane in lanes.iter_mut() {
                    for (i, s) in lane.iter_mut().enumerate() {
                        *s += rc[i];
                    }
                }
                for lane in lanes.iter_mut() {
                    lane[0] = sbox_full::<Goldilocks>(lane[0]);
                }
                for lane in lanes.iter_mut() {
                    mds_mul_scalar(lane);
                }
            }

            // Terminal full rounds.
            for rc in GOLDILOCKS_POSEIDON1_RC_8
                .iter()
                .take(POSEIDON1_N_ROUNDS)
                .skip(POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS)
            {
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

    /// Plonky3-compatibility known-answer vector.
    ///
    /// Reference: `plonky3/goldilocks/src/poseidon1.rs::tests::test_poseidon_goldilocks_width_8`
    /// — input `[0..8)`, expected output hardcoded from upstream.
    #[test]
    fn test_plonky3_compatibility() {
        use field::PrimeField64;

        let p = default_goldilocks_poseidon1_8();
        let mut input: [Goldilocks; 8] = [0, 1, 2, 3, 4, 5, 6, 7].map(Goldilocks::new);
        p.permute_mut(&mut input);
        let expected: [u64; 8] = [
            2431226948502761687,
            9427563026145807618,
            6827549936272051660,
            16907684411084503785,
            10131745626715172913,
            17448305483431576765,
            9066501914269485014,
            12095238468458521303,
        ];
        let got: [u64; 8] = input.map(|x| x.as_canonical_u64());
        assert_eq!(got, expected);
    }
}
