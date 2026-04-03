// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::sync::OnceLock;

use core::ops::Mul;

use crate::KoalaBear;
use crate::symmetric::Permutation;
use field::{Algebra, Field, InjectiveMonomial, PrimeCharacteristicRing};

pub const POSEIDON1_WIDTH: usize = 16;
pub const POSEIDON1_HALF_FULL_ROUNDS: usize = 4;
pub const POSEIDON1_PARTIAL_ROUNDS: usize = 20;
pub const POSEIDON1_SBOX_DEGREE: u64 = 3;
const POSEIDON1_N_ROUNDS: usize = 2 * POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS;

// =========================================================================
// MDS circulant matrix
// =========================================================================

/// First column of the circulant MDS matrix.
const MDS_CIRC_COL: [KoalaBear; 16] = KoalaBear::new_array([1, 3, 13, 22, 67, 2, 15, 63, 101, 1, 2, 17, 11, 1, 51, 1]);

// =========================================================================
// Forward twiddles for 16-point FFT: W_k = omega^k
// =========================================================================

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
const W1: KoalaBear = KoalaBear::new(0x6b52061e);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
const W2: KoalaBear = KoalaBear::new(0x894b5390);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
const W3: KoalaBear = KoalaBear::new(0x39f910ef);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
const W4: KoalaBear = KoalaBear::new(0x304096c9);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
const W5: KoalaBear = KoalaBear::new(0x33c5a441);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
const W6: KoalaBear = KoalaBear::new(0x2e9b3a27);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
const W7: KoalaBear = KoalaBear::new(0x9d09df4b);

// =========================================================================
// 16-point FFT / IFFT (radix-2, fully unrolled, in-place)
// =========================================================================

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[inline(always)]
fn bt<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize) {
    let (a, b) = (v[lo], v[hi]);
    v[lo] = a + b;
    v[hi] = a - b;
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[inline(always)]
fn dit<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize, t: KoalaBear) {
    let a = v[lo];
    let tb = v[hi] * t;
    v[lo] = a + tb;
    v[hi] = a - tb;
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[inline(always)]
fn neg_dif<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize, t: KoalaBear) {
    let (a, b) = (v[lo], v[hi]);
    v[lo] = a + b;
    v[hi] = (b - a) * t;
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[inline(always)]
fn dif_ifft_16_mut<R: Algebra<KoalaBear>>(f: &mut [R; 16]) {
    bt(f, 0, 8);
    neg_dif(f, 1, 9, W7);
    neg_dif(f, 2, 10, W6);
    neg_dif(f, 3, 11, W5);
    neg_dif(f, 4, 12, W4);
    neg_dif(f, 5, 13, W3);
    neg_dif(f, 6, 14, W2);
    neg_dif(f, 7, 15, W1);
    bt(f, 0, 4);
    neg_dif(f, 1, 5, W6);
    neg_dif(f, 2, 6, W4);
    neg_dif(f, 3, 7, W2);
    bt(f, 8, 12);
    neg_dif(f, 9, 13, W6);
    neg_dif(f, 10, 14, W4);
    neg_dif(f, 11, 15, W2);
    bt(f, 0, 2);
    neg_dif(f, 1, 3, W4);
    bt(f, 4, 6);
    neg_dif(f, 5, 7, W4);
    bt(f, 8, 10);
    neg_dif(f, 9, 11, W4);
    bt(f, 12, 14);
    neg_dif(f, 13, 15, W4);
    bt(f, 0, 1);
    bt(f, 2, 3);
    bt(f, 4, 5);
    bt(f, 6, 7);
    bt(f, 8, 9);
    bt(f, 10, 11);
    bt(f, 12, 13);
    bt(f, 14, 15);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[inline(always)]
fn dit_fft_16_mut<R: Algebra<KoalaBear>>(f: &mut [R; 16]) {
    bt(f, 0, 1);
    bt(f, 2, 3);
    bt(f, 4, 5);
    bt(f, 6, 7);
    bt(f, 8, 9);
    bt(f, 10, 11);
    bt(f, 12, 13);
    bt(f, 14, 15);
    bt(f, 0, 2);
    dit(f, 1, 3, W4);
    bt(f, 4, 6);
    dit(f, 5, 7, W4);
    bt(f, 8, 10);
    dit(f, 9, 11, W4);
    bt(f, 12, 14);
    dit(f, 13, 15, W4);
    bt(f, 0, 4);
    dit(f, 1, 5, W2);
    dit(f, 2, 6, W4);
    dit(f, 3, 7, W6);
    bt(f, 8, 12);
    dit(f, 9, 13, W2);
    dit(f, 10, 14, W4);
    dit(f, 11, 15, W6);
    bt(f, 0, 8);
    dit(f, 1, 9, W1);
    dit(f, 2, 10, W2);
    dit(f, 3, 11, W3);
    dit(f, 4, 12, W4);
    dit(f, 5, 13, W5);
    dit(f, 6, 14, W6);
    dit(f, 7, 15, W7);
}

// =========================================================================
// Circulant MDS via Karatsuba convolution (used for full rounds)
//
// Ported from Plonky3 mds/src/karatsuba_convolution.rs.
// Uses field arithmetic (halve + mixed dot product).
// Exploits small MDS column entries (1, 2, 3 = cheap muls).
// =========================================================================

#[inline(always)]
fn parity_dot<R: PrimeCharacteristicRing + Mul<KoalaBear, Output = R>, const N: usize>(
    lhs: [R; N],
    rhs: [KoalaBear; N],
) -> R {
    let mut acc = lhs[0] * rhs[0];
    for i in 1..N {
        acc += lhs[i] * rhs[i];
    }
    acc
}

#[inline(always)]
fn conv4<R: PrimeCharacteristicRing + Mul<KoalaBear, Output = R>>(lhs: [R; 4], rhs: [KoalaBear; 4], output: &mut [R]) {
    let u_p = [lhs[0] + lhs[2], lhs[1] + lhs[3]];
    let u_m = [lhs[0] - lhs[2], lhs[1] - lhs[3]];
    let v_p = [rhs[0] + rhs[2], rhs[1] + rhs[3]];
    let v_m = [rhs[0] - rhs[2], rhs[1] - rhs[3]];
    output[0] = parity_dot(u_m, [v_m[0], -v_m[1]]);
    output[1] = parity_dot(u_m, [v_m[1], v_m[0]]);
    output[2] = parity_dot(u_p, v_p);
    output[3] = parity_dot(u_p, [v_p[1], v_p[0]]);
    output[0] += output[2];
    output[1] += output[3];
    output[0] = output[0].halve();
    output[1] = output[1].halve();
    output[2] -= output[0];
    output[3] -= output[1];
}

#[inline(always)]
fn negacyclic_conv4<R: PrimeCharacteristicRing + Mul<KoalaBear, Output = R>>(
    lhs: [R; 4],
    rhs: [KoalaBear; 4],
    output: &mut [R],
) {
    output[0] = parity_dot(lhs, [rhs[0], -rhs[3], -rhs[2], -rhs[1]]);
    output[1] = parity_dot(lhs, [rhs[1], rhs[0], -rhs[3], -rhs[2]]);
    output[2] = parity_dot(lhs, [rhs[2], rhs[1], rhs[0], -rhs[3]]);
    output[3] = parity_dot(lhs, [rhs[3], rhs[2], rhs[1], rhs[0]]);
}

#[inline(always)]
fn conv_n_recursive<R: PrimeCharacteristicRing + Mul<KoalaBear, Output = R>, const N: usize, const H: usize>(
    lhs: [R; N],
    rhs: [KoalaBear; N],
    output: &mut [R],
    inner_conv: fn([R; H], [KoalaBear; H], &mut [R]),
    inner_neg: fn([R; H], [KoalaBear; H], &mut [R]),
) {
    let mut lp = [R::ZERO; H];
    let mut ln = [R::ZERO; H];
    let mut rp = [KoalaBear::ZERO; H];
    let mut rn = [KoalaBear::ZERO; H];
    for i in 0..H {
        lp[i] = lhs[i] + lhs[i + H];
        ln[i] = lhs[i] - lhs[i + H];
        rp[i] = rhs[i] + rhs[i + H];
        rn[i] = rhs[i] - rhs[i + H];
    }
    let (left, right) = output.split_at_mut(H);
    inner_neg(ln, rn, left);
    inner_conv(lp, rp, right);
    for i in 0..H {
        left[i] += right[i];
        left[i] = left[i].halve();
        right[i] -= left[i];
    }
}

#[inline(always)]
fn negacyclic_conv_n_recursive<
    R: PrimeCharacteristicRing + Mul<KoalaBear, Output = R>,
    const N: usize,
    const H: usize,
>(
    lhs: [R; N],
    rhs: [KoalaBear; N],
    output: &mut [R],
    inner_neg: fn([R; H], [KoalaBear; H], &mut [R]),
) {
    let mut le = [R::ZERO; H];
    let mut lo = [R::ZERO; H];
    let mut ls = [R::ZERO; H];
    let mut re = [KoalaBear::ZERO; H];
    let mut ro = [KoalaBear::ZERO; H];
    let mut rs = [KoalaBear::ZERO; H];
    for i in 0..H {
        le[i] = lhs[2 * i];
        lo[i] = lhs[2 * i + 1];
        ls[i] = le[i] + lo[i];
        re[i] = rhs[2 * i];
        ro[i] = rhs[2 * i + 1];
        rs[i] = re[i] + ro[i];
    }
    let mut es = [R::ZERO; H];
    let (left, right) = output.split_at_mut(H);
    inner_neg(le, re, &mut es);
    inner_neg(lo, ro, left);
    inner_neg(ls, rs, right);
    right[0] -= es[0] + left[0];
    es[0] -= left[H - 1];
    for i in 1..H {
        right[i] -= es[i] + left[i];
        es[i] += left[i - 1];
    }
    for i in 0..H {
        output[2 * i] = es[i];
        output[2 * i + 1] = output[i + H];
    }
}

#[inline(always)]
fn conv8<R: PrimeCharacteristicRing + Mul<KoalaBear, Output = R>>(lhs: [R; 8], rhs: [KoalaBear; 8], output: &mut [R]) {
    conv_n_recursive(lhs, rhs, output, conv4::<R>, negacyclic_conv4::<R>);
}

#[inline(always)]
fn negacyclic_conv8<R: PrimeCharacteristicRing + Mul<KoalaBear, Output = R>>(
    lhs: [R; 8],
    rhs: [KoalaBear; 8],
    output: &mut [R],
) {
    negacyclic_conv_n_recursive(lhs, rhs, output, negacyclic_conv4::<R>);
}

/// Circulant MDS multiply via Karatsuba convolution: state = C * state.
#[inline(always)]
pub fn mds_circ_16<R: PrimeCharacteristicRing + Mul<KoalaBear, Output = R>>(state: &mut [R; 16]) {
    let input = *state;
    conv_n_recursive(
        input,
        MDS_CIRC_COL,
        state.as_mut_slice(),
        conv8::<R>,
        negacyclic_conv8::<R>,
    );
}

// =========================================================================
// Sparse matrix decomposition helpers (for NEON partial rounds)
// =========================================================================

/// Dense NxN matrix multiplication: C = A * B.
fn matrix_mul_16(a: &[[KoalaBear; 16]; 16], b: &[[KoalaBear; 16]; 16]) -> [[KoalaBear; 16]; 16] {
    core::array::from_fn(|i| {
        core::array::from_fn(|j| {
            let mut s = KoalaBear::ZERO;
            for k in 0..16 {
                s += a[i][k] * b[k][j];
            }
            s
        })
    })
}

/// Matrix-vector multiplication: result = M * v.
fn matrix_vec_mul_16(m: &[[KoalaBear; 16]; 16], v: &[KoalaBear; 16]) -> [KoalaBear; 16] {
    core::array::from_fn(|i| {
        let mut s = KoalaBear::ZERO;
        for j in 0..16 {
            s += m[i][j] * v[j];
        }
        s
    })
}

/// Matrix transpose.
fn matrix_transpose_16(m: &[[KoalaBear; 16]; 16]) -> [[KoalaBear; 16]; 16] {
    core::array::from_fn(|i| core::array::from_fn(|j| m[j][i]))
}

/// NxN matrix inverse via Gauss-Jordan elimination.
fn matrix_inverse_16(m: &[[KoalaBear; 16]; 16]) -> [[KoalaBear; 16]; 16] {
    let mut aug: [[KoalaBear; 16]; 16] = *m;
    let mut inv: [[KoalaBear; 16]; 16] =
        core::array::from_fn(|i| core::array::from_fn(|j| if i == j { KoalaBear::ONE } else { KoalaBear::ZERO }));

    for col in 0..16 {
        let pivot_row = (col..16)
            .find(|&r| aug[r][col] != KoalaBear::ZERO)
            .expect("Matrix is singular");
        if pivot_row != col {
            aug.swap(col, pivot_row);
            inv.swap(col, pivot_row);
        }
        let pivot_inv = aug[col][col].inverse();
        for j in 0..16 {
            aug[col][j] *= pivot_inv;
            inv[col][j] *= pivot_inv;
        }
        for i in 0..16 {
            if i == col {
                continue;
            }
            let factor = aug[i][col];
            if factor == KoalaBear::ZERO {
                continue;
            }
            let aug_col_row = aug[col];
            let inv_col_row = inv[col];
            for j in 0..16 {
                aug[i][j] -= factor * aug_col_row[j];
                inv[i][j] -= factor * inv_col_row[j];
            }
        }
    }
    inv
}

/// Inverse of the 15x15 bottom-right submatrix of m.
fn submatrix_inverse_15(m: &[[KoalaBear; 16]; 16]) -> [[KoalaBear; 15]; 15] {
    let mut sub: [[KoalaBear; 15]; 15] = core::array::from_fn(|i| core::array::from_fn(|j| m[i + 1][j + 1]));
    let mut inv: [[KoalaBear; 15]; 15] =
        core::array::from_fn(|i| core::array::from_fn(|j| if i == j { KoalaBear::ONE } else { KoalaBear::ZERO }));

    for col in 0..15 {
        let pivot_row = (col..15)
            .find(|&r| sub[r][col] != KoalaBear::ZERO)
            .expect("Submatrix is singular");
        if pivot_row != col {
            sub.swap(col, pivot_row);
            inv.swap(col, pivot_row);
        }
        let pivot_inv = sub[col][col].inverse();
        for j in 0..15 {
            sub[col][j] *= pivot_inv;
            inv[col][j] *= pivot_inv;
        }
        for i in 0..15 {
            if i == col {
                continue;
            }
            let factor = sub[i][col];
            if factor == KoalaBear::ZERO {
                continue;
            }
            let sub_col_row = sub[col];
            let inv_col_row = inv[col];
            for j in 0..15 {
                sub[i][j] -= factor * sub_col_row[j];
                inv[i][j] -= factor * inv_col_row[j];
            }
        }
    }
    inv
}

type SparseMatrices = ([[KoalaBear; 16]; 16], Vec<[KoalaBear; 16]>, Vec<[KoalaBear; 16]>);

/// Factor the dense MDS matrix into POSEIDON1_PARTIAL_ROUNDS sparse matrices.
/// Returns (m_i, v_collection, w_hat_collection) in forward application order.
fn compute_equivalent_matrices(mds: &[[KoalaBear; 16]; 16]) -> SparseMatrices {
    let rounds_p = POSEIDON1_PARTIAL_ROUNDS;
    let mut w_hat_collection: Vec<[KoalaBear; 16]> = Vec::with_capacity(rounds_p);
    let mut v_collection: Vec<[KoalaBear; 16]> = Vec::with_capacity(rounds_p);

    let mds_t = matrix_transpose_16(mds);
    let mut m_mul = mds_t;
    let mut m_i = [[KoalaBear::ZERO; 16]; 16];

    for _ in 0..rounds_p {
        // v = first row of m_mul (excluding [0,0]), padded with 0 at end.
        let v_arr: [KoalaBear; 16] = core::array::from_fn(|j| if j < 15 { m_mul[0][j + 1] } else { KoalaBear::ZERO });

        // w = first column of m_mul (excluding [0,0]).
        let w: [KoalaBear; 15] = core::array::from_fn(|i| m_mul[i + 1][0]);

        // M̂^{-1} (inverse of bottom-right 15x15 submatrix).
        let m_hat_inv = submatrix_inverse_15(&m_mul);

        // ŵ = M̂^{-1} * w, padded with 0 at end.
        let w_hat_arr: [KoalaBear; 16] = core::array::from_fn(|i| {
            if i < 15 {
                let mut s = KoalaBear::ZERO;
                for k in 0..15 {
                    s += m_hat_inv[i][k] * w[k];
                }
                s
            } else {
                KoalaBear::ZERO
            }
        });

        v_collection.push(v_arr);
        w_hat_collection.push(w_hat_arr);

        // Build m_i: keep m_mul but zero first row/col, set [0,0]=1.
        m_i = m_mul;
        m_i[0][0] = KoalaBear::ONE;
        for row in m_i.iter_mut().skip(1) {
            row[0] = KoalaBear::ZERO;
        }
        for elem in m_i[0].iter_mut().skip(1) {
            *elem = KoalaBear::ZERO;
        }

        // m_mul = M^T * m_i.
        m_mul = matrix_mul_16(&mds_t, &m_i);
    }

    // Transpose m_i back.
    let m_i_returned = matrix_transpose_16(&m_i);

    // Reverse: HorizenLabs computes in reverse order.
    v_collection.reverse();
    w_hat_collection.reverse();

    (m_i_returned, v_collection, w_hat_collection)
}

/// Compress round constants via backward substitution through MDS^{-1}.
/// Returns (first_round_constants, scalar_round_constants).
fn equivalent_round_constants(
    partial_rc: &[[KoalaBear; 16]],
    mds_inv: &[[KoalaBear; 16]; 16],
) -> ([KoalaBear; 16], Vec<KoalaBear>) {
    let rounds_p = partial_rc.len();
    let mut opt_partial_rc = vec![KoalaBear::ZERO; rounds_p];

    let mut tmp = partial_rc[rounds_p - 1];
    for i in (0..rounds_p - 1).rev() {
        let inv_cip = matrix_vec_mul_16(mds_inv, &tmp);
        opt_partial_rc[i + 1] = inv_cip[0];
        tmp = partial_rc[i];
        for j in 1..16 {
            tmp[j] += inv_cip[j];
        }
    }

    let first_round_constants = tmp;
    let scalar_constants = opt_partial_rc[1..].to_vec();
    (first_round_constants, scalar_constants)
}

// =========================================================================
// Precomputed constants (stored in struct, OnceLock only at construction)
// =========================================================================

#[derive(Debug)]
struct Precomputed {
    // --- Sparse matrix decomposition ---
    /// First round constant vector (full width), added once before m_i multiply.
    sparse_first_round_constants: [KoalaBear; 16],
    /// Dense transition matrix m_i, applied once before the partial round loop.
    sparse_m_i: [[KoalaBear; 16]; 16],
    /// Per-round full first row: [mds_0_0, ŵ[0], ..., ŵ[14]].
    /// Length = POSEIDON1_PARTIAL_ROUNDS.
    sparse_first_row: Vec<[KoalaBear; 16]>,
    /// Per-round first-column vectors (excluding [0,0]).
    /// `v[r]` = [v[0], ..., v[14], 0]. Length = POSEIDON1_PARTIAL_ROUNDS.
    sparse_v: Vec<[KoalaBear; 16]>,
    /// Scalar constants for partial rounds 0..RP-2.
    /// Length = POSEIDON1_PARTIAL_ROUNDS - 1.
    sparse_round_constants: Vec<KoalaBear>,

    // --- NEON pre-packed constants ---
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    neon: NeonPrecomputed,
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
struct NeonPrecomputed {
    /// Initial full round constants in negative NEON form (only first 3 rounds;
    /// the 4th is fused with the partial round entry).
    packed_initial_rc: [[core::arch::aarch64::uint32x4_t; 16]; POSEIDON1_HALF_FULL_ROUNDS - 1],
    /// Terminal full round constants in canonical form.
    packed_terminal_rc: [[core::arch::aarch64::uint32x4_t; 16]; POSEIDON1_HALF_FULL_ROUNDS],
    /// Pre-packed sparse first rows as PackedKoalaBearNeon.
    packed_sparse_first_row: [[PackedKB; 16]; POSEIDON1_PARTIAL_ROUNDS],
    /// Pre-packed v vectors as PackedKoalaBearNeon.
    packed_sparse_v: [[PackedKB; 16]; POSEIDON1_PARTIAL_ROUNDS],
    /// Pre-packed scalar round constants for partial rounds 0..RP-2.
    packed_round_constants: [PackedKB; POSEIDON1_PARTIAL_ROUNDS - 1],
    /// Fused matrix: m_i * MDS * state_after_last_initial_sbox + m_i * first_rc.
    /// Replaces: FFT MDS + add first_rc + dense m_i → single dense multiply.
    packed_fused_mi_mds: [[PackedKB; 16]; 16],
    /// Fused bias: m_i * first_round_constants.
    packed_fused_bias: [PackedKB; 16],
    /// Last initial round constant in canonical form (for add_rc_and_sbox).
    packed_last_initial_rc: [core::arch::aarch64::uint32x4_t; 16],
    /// Pre-packed eigenvalues * INV16 for FFT MDS (absorbs /16 normalization).
    packed_lambda_over_16: [PackedKB; 16],
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl std::fmt::Debug for NeonPrecomputed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NeonPrecomputed").finish_non_exhaustive()
    }
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
type FP = crate::KoalaBearParameters;
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
type PackedKB = crate::PackedKoalaBearNeon;

static PRECOMPUTED: OnceLock<Precomputed> = OnceLock::new();

fn precomputed() -> &'static Precomputed {
    PRECOMPUTED.get_or_init(|| {
        // Dense MDS for sparse decomposition.
        let mds: [[KoalaBear; 16]; 16] =
            core::array::from_fn(|i| core::array::from_fn(|j| MDS_CIRC_COL[(16 + i - j) % 16]));

        let partial_rc =
            &POSEIDON1_RC[POSEIDON1_HALF_FULL_ROUNDS..POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS];

        // --- Sparse matrix decomposition constants ---
        let mds_inv = matrix_inverse_16(&mds);
        let (first_round_constants, scalar_round_constants) = equivalent_round_constants(partial_rc, &mds_inv);
        let (m_i, sparse_v, sparse_w_hat) = compute_equivalent_matrices(&mds);

        // Pre-assemble full first rows: [mds_0_0, ŵ[0], ..., ŵ[14]].
        let mds_0_0 = mds[0][0];
        let sparse_first_row: Vec<[KoalaBear; 16]> = sparse_w_hat
            .iter()
            .map(|w| core::array::from_fn(|i| if i == 0 { mds_0_0 } else { w[i - 1] }))
            .collect();

        // --- NEON pre-packed constants ---
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        let neon = {
            use crate::PackedMontyField31Neon;
            use crate::convert_to_vec_neon;

            let pack = |c: KoalaBear| PackedMontyField31Neon::<FP>::from(c);
            let canon_form = |c: KoalaBear| convert_to_vec_neon::<FP>(c.value);

            // Initial full round constants (only first 3; 4th is fused).
            let init_rc = poseidon1_initial_constants();
            let packed_initial_rc: [[core::arch::aarch64::uint32x4_t; 16]; POSEIDON1_HALF_FULL_ROUNDS - 1] =
                core::array::from_fn(|r| init_rc[r].map(canon_form));

            // Last initial round constant (for add_rc_and_sbox before partial rounds).
            let packed_last_initial_rc = init_rc[POSEIDON1_HALF_FULL_ROUNDS - 1].map(canon_form);

            // Terminal full round constants.
            let term_rc = poseidon1_final_constants();
            let packed_terminal_rc: [[core::arch::aarch64::uint32x4_t; 16]; POSEIDON1_HALF_FULL_ROUNDS] =
                core::array::from_fn(|r| term_rc[r].map(canon_form));

            // Pre-packed sparse constants (fixed-size arrays).
            let packed_sparse_first_row: [[PackedKB; 16]; POSEIDON1_PARTIAL_ROUNDS] =
                core::array::from_fn(|r| sparse_first_row[r].map(pack));
            let packed_sparse_v: [[PackedKB; 16]; POSEIDON1_PARTIAL_ROUNDS] =
                core::array::from_fn(|r| sparse_v[r].map(pack));
            let packed_round_constants: [PackedKB; POSEIDON1_PARTIAL_ROUNDS - 1] =
                core::array::from_fn(|r| pack(scalar_round_constants[r]));

            // Fused matrix: (m_i * MDS), replaces last initial FFT MDS + add first_rc + m_i.
            let fused_mi_mds = matrix_mul_16(&m_i, &mds);
            let packed_fused_mi_mds: [[PackedKB; 16]; 16] = core::array::from_fn(|i| fused_mi_mds[i].map(pack));

            // Fused bias: m_i * first_round_constants.
            let fused_bias = matrix_vec_mul_16(&m_i, &first_round_constants);
            let packed_fused_bias: [PackedKB; 16] = fused_bias.map(pack);

            // Pre-packed eigenvalues * INV16 (absorbs /16 into eigenvalues).
            let mut lambda_br = MDS_CIRC_COL;
            dif_ifft_16_mut(&mut lambda_br);
            let inv16 = KoalaBear::new(3932160001); // 16^{-1} mod p
            let packed_lambda_over_16: [PackedKB; 16] = core::array::from_fn(|i| pack(lambda_br[i] * inv16));

            NeonPrecomputed {
                packed_initial_rc,
                packed_terminal_rc,
                packed_sparse_first_row,
                packed_sparse_v,
                packed_round_constants,
                packed_fused_mi_mds,
                packed_fused_bias,
                packed_last_initial_rc,
                packed_lambda_over_16,
            }
        };

        Precomputed {
            sparse_first_round_constants: first_round_constants,
            sparse_m_i: m_i,
            sparse_first_row,
            sparse_v,
            sparse_round_constants: scalar_round_constants,
            #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
            neon,
        }
    })
}

// =========================================================================
// Round constants (Grain LFSR, matching Plonky3)
// =========================================================================

const POSEIDON1_RC: [[KoalaBear; 16]; POSEIDON1_N_ROUNDS] = KoalaBear::new_2d_array([
    // Initial full rounds (4)
    [
        0x16563297, 0x3e669663, 0xad043724, 0x90ce7116, 0xa078ea37, 0x0626b030, 0xec75cf01, 0x3aab2bf5, 0x591c1f83,
        0x3c9a00ec, 0x73c17410, 0x0b7b4103, 0x00f0d14d, 0x59c6c3d4, 0x569c4787, 0x29f72a6a,
    ],
    [
        0xe7e6145a, 0xa62dfa56, 0xa72459c4, 0xc12e3d21, 0xcfbaf427, 0x79471bf4, 0x35ea3fd2, 0x0e871da2, 0xb8142f08,
        0x3623564d, 0x607e0747, 0x6c2c3f6a, 0xbaa4cd3d, 0x069d6b42, 0xb98024b9, 0x68831d77,
    ],
    [
        0xbc4cdd4a, 0x872186a1, 0x90c3888e, 0x7e783120, 0xb3575851, 0x334e7976, 0xbaa135c3, 0x3eb628cc, 0x58712a8d,
        0xd8c18178, 0x602d3f41, 0xcb1b656a, 0x5bd99496, 0xf1f622ca, 0xc363a444, 0x97c4b605,
    ],
    [
        0x5a07e287, 0xc80962f3, 0x2e37f2d9, 0x26d67c3e, 0xcf96a0a0, 0x1fcde991, 0x641f2cd8, 0x1ef5c127, 0xaddf98c2,
        0xa5c96cb9, 0xca07faa8, 0x73d4e273, 0x8385bfa3, 0x15b22541, 0xcbfde37c, 0x32475586,
    ],
    // Partial rounds (20)
    [
        0xe49f77a8, 0xc751c2d1, 0x76eb1c5a, 0x8b8672cd, 0x1cb44174, 0xf6fb3e5e, 0xdaabb8d4, 0x18e7bd3d, 0x2a560e97,
        0xe04179a3, 0xe21d103d, 0x58d0e0ab, 0x303d1e0c, 0x3f250c3c, 0xc86d7c1e, 0x3ece5680,
    ],
    [
        0x16b1f692, 0xf16b95b7, 0x26701f28, 0x85cf7a29, 0xe40a08a9, 0x9636d8d1, 0xeb72850a, 0x48143205, 0x73afec23,
        0x7fd31200, 0xd1fc60c6, 0xce74b7f9, 0xe0acb139, 0x59eeab1f, 0x18afb097, 0x42d20438,
    ],
    [
        0xcaf14d2f, 0xf26c3fe2, 0x2adc5737, 0xe1e64e39, 0x735ae3e8, 0xbb1e61db, 0xb7c7035c, 0xae582686, 0xebfaf2bd,
        0x0e0610a8, 0x8cd868de, 0xc68befce, 0x6cc077e3, 0x73b6bf4f, 0x8e8404bb, 0x056c9356,
    ],
    [
        0xe2458a7a, 0x895a2ec9, 0xe3667424, 0x68d98c49, 0x044ed7f5, 0x8139cd81, 0x32fe0a12, 0xa9f206ee, 0x7ec87d9b,
        0xa4854877, 0xdd8cec50, 0x4c5d8b26, 0xe00c0ef4, 0x5da03424, 0xceb8fe3d, 0x60d7a6e2,
    ],
    [
        0x45439320, 0x99febd74, 0xf5913c65, 0x4e96d0aa, 0xc7653152, 0x90cd4ba6, 0x8889cbcd, 0x6638fae2, 0xdcfc4c5e,
        0x8af12cc1, 0x59307544, 0xe1e6bbb3, 0xf9bfa656, 0x72ae4f2c, 0xd5c9598d, 0x3ad1558f,
    ],
    [
        0x2a3ca52b, 0x99b09e2f, 0x2f7eecd5, 0x520ae1bb, 0x64587b54, 0xf8562fb2, 0xd7770959, 0x60406484, 0x530479ec,
        0x12a21d02, 0xac8bad07, 0xf67994c0, 0x0cc0472e, 0x18c6d644, 0x1b664e25, 0xe6e8b908,
    ],
    [
        0xb2983e38, 0x47455654, 0x17526a2f, 0x6a2d789f, 0xe74a8306, 0xe0fb4aad, 0x9cd3cd7b, 0x614971b7, 0xd97aac83,
        0x3e042505, 0x3125d6a4, 0x562bac89, 0x95736c1d, 0xd58f393b, 0x58cd5712, 0x90841a10,
    ],
    [
        0x31eadbdb, 0x2ea63f0b, 0xb7911a51, 0x39001e47, 0x89687d2d, 0x77f8f4db, 0x4077716d, 0xe74357fd, 0x02f591df,
        0x1b9d1ab6, 0xc10be6ba, 0x9d5ad139, 0x3af0f7c7, 0x5a63730e, 0x606a08dd, 0x8e896d67,
    ],
    [
        0x3cafe446, 0x39b28d39, 0xcd38a868, 0x56c4c0ed, 0x692a0c89, 0x662f9fed, 0x8a312370, 0x65998ae3, 0x5ab80205,
        0xc2b3941d, 0xcf73f6ba, 0x105cd3df, 0x5cd190f4, 0x6f9d0294, 0x7c96a0cd, 0x41c10f0d,
    ],
    [
        0x672380d2, 0x30215c93, 0xce6489d2, 0xd9759689, 0x92102223, 0x79ff0e1b, 0x8180a72a, 0x1d1d6066, 0x1257b35f,
        0xb130f5f7, 0x14b2bfe1, 0xc1eb9e61, 0x9a032f74, 0x3922de50, 0x22ac5b30, 0x52152927,
    ],
    [
        0xd03de930, 0xd30282b3, 0x96637fce, 0xf5b04144, 0x5c659f82, 0x3f257b92, 0xf471e073, 0x64d033e2, 0x489b2abb,
        0x25fcf9fd, 0x7e528a59, 0x042f3e11, 0x55a5b0eb, 0x6ceb509d, 0x331c2be5, 0xc59c27ab,
    ],
    [
        0x4fe6f17b, 0xd38fd166, 0x807c01b6, 0x81a24eb2, 0xbdc42437, 0x9f81c56c, 0xafeedd34, 0x3bf25434, 0x2bacd3b8,
        0x53b1e339, 0x39d7e7d9, 0xd79c8cd0, 0x889aa21b, 0x6de4d734, 0x2a3486a9, 0xc6bda81d,
    ],
    [
        0x1b7b6b5d, 0x0b3a9554, 0xda9f90a6, 0xbf99a500, 0xa6fdac71, 0xc647ce05, 0x08c13cba, 0x1afb4dba, 0x924e49e0,
        0xd945c1b8, 0xb27617db, 0x8925b96f, 0x11276cf2, 0x2a04b3ea, 0xe740b35c, 0x8e599926,
    ],
    [
        0xf2172870, 0x4637c7d7, 0x1f3f2c3b, 0x523dc658, 0x8b9be7a3, 0x5c3edbc1, 0x710f3163, 0x817dcef3, 0x9bb5931d,
        0xc9fedd06, 0x5452d0ff, 0x3c3fb0bb, 0x46c83153, 0xd782c351, 0x5d16354f, 0x486081bc,
    ],
    [
        0x7ef8fd4c, 0x5bd0b96b, 0x507531e5, 0x921f01bf, 0x57aae86e, 0x50f668df, 0x9cd98fa7, 0xb8ef69b5, 0x33f83af2,
        0xef0e4b26, 0x3f502d46, 0x723a0147, 0x7b2df793, 0x9e0dab32, 0x2108bd31, 0x0e64b870,
    ],
    [
        0x2005322b, 0x34b37a14, 0x326a4764, 0xc23709a9, 0xc2877e3f, 0x98d3bc14, 0x071198ef, 0x9dd541db, 0xa47318c5,
        0xca4336f1, 0xde35cddb, 0x94dd1390, 0xa74cfcc5, 0x71396cbd, 0x08456022, 0x040cbdb3,
    ],
    [
        0x837945ce, 0x9e49261c, 0x28632ae3, 0xe2ebb5e1, 0x13035665, 0x059623df, 0x97dc3043, 0xa04168fc, 0x2a936478,
        0x0047f358, 0xf04d99cc, 0x7ea282bc, 0xdb61c7a1, 0x36213a96, 0x967c85a3, 0x7f9822e0,
    ],
    [
        0xb6954f09, 0x07292e31, 0x02091a8d, 0xa304c184, 0x70ea38a0, 0xd3053ca7, 0x00b561ee, 0xc70e3fcb, 0xc82103f8,
        0xdd6355cf, 0x5f0b2b85, 0x6194184e, 0x64fb4fdf, 0x2aaf8ca7, 0x40c2422b, 0x176a2fc8,
    ],
    [
        0x7cc97de7, 0x63be86dc, 0x08f0ca90, 0x3071a41e, 0xd56e3a1f, 0xf220dce4, 0x5424c61e, 0xc14b44d7, 0xe4f646df,
        0x6d7be7ad, 0x4b29772e, 0x07ba3bce, 0x397a901c, 0xd710cf8c, 0x018d1e0b, 0x6829ef3d,
    ],
    [
        0x9ba21d4c, 0xed64b8db, 0x4aaec707, 0x6d6ae164, 0x3c0746a4, 0xc15cdc64, 0x36e921d7, 0x30c898cc, 0x7c981c6e,
        0x871c3b04, 0x7050a49b, 0x819149a2, 0x08bc501d, 0xc26ceeae, 0x3d78eddc, 0xf2884eca,
    ],
    // Terminal full rounds (4)
    [
        0x4602cc03, 0xa906d37f, 0x4f1b5c39, 0xc46d832b, 0x189335a1, 0xaa11ab5e, 0xec647d5a, 0x1cae1926, 0x9e51dd38,
        0xbf44201e, 0x371adb90, 0x7a544001, 0x58d3f484, 0x195ec3a6, 0x45776d19, 0x09e98d4a,
    ],
    [
        0x29f2e1d8, 0x2d7f058c, 0xf25f4a33, 0x4352dfef, 0xa74c0aef, 0x52ba24ca, 0x677b305b, 0xf2941d7d, 0xda68d6e0,
        0x32502a90, 0x0fedb550, 0xf5b7cb9b, 0xcad9d395, 0x793f2d86, 0xa49167fa, 0x8a86b259,
    ],
    [
        0xabb033c5, 0xe1562215, 0x64e88ed0, 0xb9194068, 0xaf17ebfb, 0xee8377ad, 0xcc7cefea, 0x2522c0b2, 0xa507ae8e,
        0x6eeb4ced, 0x7980c048, 0x25a6f40d, 0xdd443b41, 0x8412e868, 0xbd05f0f4, 0x8c804a4e,
    ],
    [
        0xbaad5dad, 0x2bdbe1f0, 0x8dfe8a3f, 0xa5b6f683, 0x0de5ca68, 0x5af48e3d, 0x5d895c2f, 0xf656679d, 0xa3d98a66,
        0xb5e70bc2, 0x678a0ba2, 0x05441e51, 0x5785e092, 0x59734838, 0x4118c3c6, 0xe2e29ed7,
    ],
]);

// =========================================================================
// Accessors
// =========================================================================

pub fn poseidon1_round_constants() -> &'static [[KoalaBear; 16]; POSEIDON1_N_ROUNDS] {
    &POSEIDON1_RC
}

#[inline(always)]
pub fn poseidon1_initial_constants() -> &'static [[KoalaBear; 16]] {
    &POSEIDON1_RC[..POSEIDON1_HALF_FULL_ROUNDS]
}

#[inline(always)]
pub fn poseidon1_partial_constants() -> &'static [[KoalaBear; 16]] {
    &POSEIDON1_RC[POSEIDON1_HALF_FULL_ROUNDS..POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS]
}

#[inline(always)]
pub fn poseidon1_final_constants() -> &'static [[KoalaBear; 16]] {
    &POSEIDON1_RC[POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS..]
}

pub fn poseidon1_sparse_m_i() -> &'static [[KoalaBear; 16]; 16] {
    &precomputed().sparse_m_i
}

/// Per-round first row: `[mds_0_0, ŵ[0], ..., ŵ[14]]`.  Length = PARTIAL_ROUNDS.
pub fn poseidon1_sparse_first_row() -> &'static Vec<[KoalaBear; 16]> {
    &precomputed().sparse_first_row
}

/// Per-round rank-1 update vectors `v[r]`.  `v[r][0..14]` are the 15 update coefficients
/// (index 15 is always zero).  Length = PARTIAL_ROUNDS.
pub fn poseidon1_sparse_v() -> &'static Vec<[KoalaBear; 16]> {
    &precomputed().sparse_v
}

/// Full-width constant vector added once before the `m_i` multiply.
pub fn poseidon1_sparse_first_round_constants() -> &'static [KoalaBear; 16] {
    &precomputed().sparse_first_round_constants
}

/// Scalar constants added to `state[0]` in partial rounds 0..RP-2. Length = RP-1.
pub fn poseidon1_sparse_scalar_round_constants() -> &'static Vec<KoalaBear> {
    &precomputed().sparse_round_constants
}

#[derive(Clone, Debug)]
pub struct Poseidon1KoalaBear16 {
    pre: &'static Precomputed,
}

impl Poseidon1KoalaBear16 {
    #[inline(always)]
    #[allow(clippy::needless_range_loop)]
    fn permute_generic<R: Algebra<KoalaBear> + InjectiveMonomial<3>>(&self, state: &mut [R; 16]) {
        // Initial full rounds.
        for rc in poseidon1_initial_constants() {
            Self::full_round(state, rc);
        }

        // --- Partial rounds via sparse matrix decomposition ---
        // Add first-round constants.
        for (s, &c) in state.iter_mut().zip(self.pre.sparse_first_round_constants.iter()) {
            *s += c;
        }
        // Apply dense transition matrix m_i (once).
        {
            let input = *state;
            for i in 0..16 {
                state[i] = R::ZERO;
                for j in 0..16 {
                    state[i] += input[j] * self.pre.sparse_m_i[i][j];
                }
            }
        }
        // Loop over partial rounds: S-box + scalar constant + sparse matmul.
        for r in 0..POSEIDON1_PARTIAL_ROUNDS {
            state[0] = state[0].injective_exp_n();
            if r < POSEIDON1_PARTIAL_ROUNDS - 1 {
                state[0] += self.pre.sparse_round_constants[r];
            }
            // Sparse matrix multiply: O(16) per round.
            let old_s0 = state[0];
            state[0] = parity_dot(*state, self.pre.sparse_first_row[r]);
            for i in 1..16 {
                state[i] += old_s0 * self.pre.sparse_v[r][i - 1];
            }
        }

        // Terminal full rounds.
        for rc in poseidon1_final_constants() {
            Self::full_round(state, rc);
        }
    }

    #[inline(always)]
    fn full_round<R: Algebra<KoalaBear> + InjectiveMonomial<3>>(state: &mut [R; 16], rc: &[KoalaBear; 16]) {
        for (s, &c) in state.iter_mut().zip(rc.iter()) {
            *s += c;
        }
        for s in state.iter_mut() {
            *s = s.injective_exp_n();
        }
        mds_circ_16(state);
    }

    /// NEON-specific fast path using:
    ///  - Fused AddRC+S-box (`add_rc_and_sbox`) for full rounds
    ///  - `InternalLayer16` split for ILP between S-box and dot product in partial rounds
    ///  - Pre-packed sparse matrix constants
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    #[inline(always)]
    fn permute_neon(&self, state: &mut [PackedKB; 16]) {
        use crate::PackedMontyField31Neon;
        use crate::exp_small;
        use crate::{InternalLayer16, add_rc_and_sbox};
        use core::mem::transmute;

        let neon = &self.pre.neon;
        let lambda16 = &neon.packed_lambda_over_16;

        /// FFT MDS: state = C * state.
        /// Uses lambda/16 eigenvalues so no separate /16 step needed.
        /// C * x = DIT_FFT((lambda/16) ⊙ DIF_IFFT(x))
        #[inline(always)]
        fn mds_fft_neon(state: &mut [PackedKB; 16], lambda16: &[PackedKB; 16]) {
            dif_ifft_16_mut(state);
            for i in 0..16 {
                state[i] *= lambda16[i];
            }
            dit_fft_16_mut(state);
        }

        // --- Initial full rounds (first 3 of 4) ---
        for round_constants in &neon.packed_initial_rc {
            for (s, &rc) in state.iter_mut().zip(round_constants.iter()) {
                add_rc_and_sbox::<FP, 3>(s, rc);
            }
            mds_fft_neon(state, lambda16);
        }

        // --- Last initial full round: AddRC + S-box, then fused (m_i * MDS) ---
        // Fuses: MDS(state) + first_rc → m_i * (MDS(state) + first_rc)
        //      = (m_i * MDS) * state + m_i * first_rc
        // Saves one full FFT MDS call.
        {
            for (s, &rc) in state.iter_mut().zip(neon.packed_last_initial_rc.iter()) {
                add_rc_and_sbox::<FP, 3>(s, rc);
            }
            let input = *state;
            for (i, state_i) in state.iter_mut().enumerate() {
                *state_i = PackedMontyField31Neon::<FP>::dot_product(&input, &neon.packed_fused_mi_mds[i])
                    + neon.packed_fused_bias[i];
            }
        }

        // --- Partial rounds loop with latency hiding via InternalLayer16 split ---
        {
            let mut split = InternalLayer16::from_packed_field_array(*state);

            for r in 0..POSEIDON1_PARTIAL_ROUNDS {
                // PATH A (high latency): S-box on s0 only.
                unsafe {
                    let s0_vec = split.s0.to_vector();
                    let s0_sboxed = exp_small::<FP, 3>(s0_vec);
                    split.s0 = PackedMontyField31Neon::from_vector(s0_sboxed);
                }

                // Add scalar round constant (except last round).
                if r < POSEIDON1_PARTIAL_ROUNDS - 1 {
                    split.s0 += neon.packed_round_constants[r];
                }

                // PATH B (can overlap with S-box): partial dot product on s_hi.
                let s_hi: &[PackedKB; 15] = unsafe { transmute(&split.s_hi) };
                let first_row = &neon.packed_sparse_first_row[r];
                let first_row_hi: &[PackedKB; 15] = first_row[1..].try_into().unwrap();
                let partial_dot = PackedMontyField31Neon::<FP>::dot_product(s_hi, first_row_hi);

                // SERIAL: complete s0 = first_row[0] * s0 + partial_dot.
                let s0_val = split.s0;
                split.s0 = s0_val * first_row[0] + partial_dot;

                // Rank-1 update: s_hi[j] += s0_old * v[j].
                let v = &neon.packed_sparse_v[r];
                let s_hi_mut: &mut [PackedKB; 15] = unsafe { transmute(&mut split.s_hi) };
                for j in 0..15 {
                    s_hi_mut[j] += s0_val * v[j];
                }
            }

            *state = unsafe { split.to_packed_field_array() };
        }

        // --- Terminal full rounds ---
        for round_constants in &neon.packed_terminal_rc {
            for (s, &rc) in state.iter_mut().zip(round_constants.iter()) {
                add_rc_and_sbox::<FP, 3>(s, rc);
            }
            mds_fft_neon(state, lambda16);
        }
    }

    /// Compression mode: output = permute(input) + input.
    #[inline(always)]
    pub fn compress_in_place<R: Algebra<KoalaBear> + InjectiveMonomial<3> + Send + Sync + 'static>(
        &self,
        state: &mut [R; 16],
    ) {
        let initial = *state;
        // Use permute_mut for NEON dispatch.
        Permutation::permute_mut(self, state);
        for (s, init) in state.iter_mut().zip(initial) {
            *s += init;
        }
    }
}

impl<R: Algebra<KoalaBear> + InjectiveMonomial<3> + Send + Sync + 'static> Permutation<[R; 16]>
    for Poseidon1KoalaBear16
{
    fn permute_mut(&self, input: &mut [R; 16]) {
        // On aarch64+neon, dispatch to the NEON fast path when R is PackedKoalaBearNeon.
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        {
            if std::any::TypeId::of::<R>() == std::any::TypeId::of::<PackedKB>() {
                // SAFETY: We have just confirmed via TypeId that R == PackedKB.
                // Both types have the same size and alignment (PackedKB is repr(transparent)).
                let neon_state: &mut [PackedKB; 16] = unsafe { &mut *(input as *mut [R; 16] as *mut [PackedKB; 16]) };
                self.permute_neon(neon_state);
                return;
            }
        }
        self.permute_generic(input);
    }
}

pub fn default_koalabear_poseidon1_16() -> Poseidon1KoalaBear16 {
    Poseidon1KoalaBear16 { pre: precomputed() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::KoalaBear;
    use field::PrimeField32;

    #[test]
    fn test_plonky3_compatibility() {
        /*
        use p3_symmetric::Permutation;

        use crate::{KoalaBear, default_koalabear_poseidon1_16};

        #[test]
        fn plonky3_test() {
            let poseidon1 = default_koalabear_poseidon1_16();
            let mut input: [KoalaBear; 16] =
                KoalaBear::new_array([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
            poseidon1.permute_mut(&mut input);
            dbg!(&input);
        }

        */
        let p1 = default_koalabear_poseidon1_16();
        let mut input: [KoalaBear; 16] = KoalaBear::new_array([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
        p1.permute_mut(&mut input);
        let vals: Vec<u32> = input.iter().map(|x| x.as_canonical_u32()).collect();
        assert_eq!(
            vals,
            vec![
                610090613, 935319874, 1893335292, 796792199, 356405232, 552237741, 55134556, 1215104204, 1823723405,
                1133298033, 1780633798, 1453946561, 710069176, 1128629550, 1917333254, 1175481618,
            ]
        );
    }
}
