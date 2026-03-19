// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::sync::OnceLock;

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

const W1: KoalaBear = KoalaBear::new(0x08dbd69c);
const W2: KoalaBear = KoalaBear::new(0x6832fe4a);
const W3: KoalaBear = KoalaBear::new(0x27ae21e2);
const W4: KoalaBear = KoalaBear::new(0x7e010002);
const W5: KoalaBear = KoalaBear::new(0x3a89a025);
const W6: KoalaBear = KoalaBear::new(0x174e3650);
const W7: KoalaBear = KoalaBear::new(0x27dfce22);

// =========================================================================
// 16-point FFT / IFFT (radix-2, fully unrolled, in-place)
// =========================================================================

#[inline(always)]
fn bt<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize) {
    let (a, b) = (v[lo], v[hi]);
    v[lo] = a + b;
    v[hi] = a - b;
}

#[inline(always)]
fn dit<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize, t: KoalaBear) {
    let a = v[lo];
    let tb = v[hi] * t;
    v[lo] = a + tb;
    v[hi] = a - tb;
}

#[inline(always)]
fn neg_dif<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize, t: KoalaBear) {
    let (a, b) = (v[lo], v[hi]);
    v[lo] = a + b;
    v[hi] = (b - a) * t;
}

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
// Circulant MDS via FFT (used for partial rounds in frequency domain)
// =========================================================================

/// Circulant MDS multiply via FFT: state = C * state.
/// C * x = (1/16) * DIT_FFT(lambda ⊙ DIF_IFFT(x))
#[allow(dead_code)]
#[inline(always)]
fn mds_fft_16<R: Algebra<KoalaBear>>(state: &mut [R; 16], lambda: &[KoalaBear; 16]) {
    dif_ifft_16_mut(state);
    for i in 0..16 {
        state[i] *= lambda[i];
    }
    dit_fft_16_mut(state);
    for s in state.iter_mut() {
        *s = s.div_2exp_u64(4);
    }
}

// =========================================================================
// Circulant MDS via Karatsuba convolution (used for full rounds)
//
// Ported from Plonky3 mds/src/karatsuba_convolution.rs.
// Uses field arithmetic (halve + mixed dot product).
// Exploits small MDS column entries (1, 2, 3 = cheap muls).
// =========================================================================

#[inline(always)]
fn parity_dot<R: Algebra<KoalaBear>, const N: usize>(lhs: [R; N], rhs: [KoalaBear; N]) -> R {
    let mut acc = lhs[0] * rhs[0];
    for i in 1..N {
        acc += lhs[i] * rhs[i];
    }
    acc
}

#[inline(always)]
fn conv4<R: Algebra<KoalaBear>>(lhs: [R; 4], rhs: [KoalaBear; 4], output: &mut [R]) {
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
fn negacyclic_conv4<R: Algebra<KoalaBear>>(lhs: [R; 4], rhs: [KoalaBear; 4], output: &mut [R]) {
    output[0] = parity_dot(lhs, [rhs[0], -rhs[3], -rhs[2], -rhs[1]]);
    output[1] = parity_dot(lhs, [rhs[1], rhs[0], -rhs[3], -rhs[2]]);
    output[2] = parity_dot(lhs, [rhs[2], rhs[1], rhs[0], -rhs[3]]);
    output[3] = parity_dot(lhs, [rhs[3], rhs[2], rhs[1], rhs[0]]);
}

#[inline(always)]
fn conv_n_recursive<R: Algebra<KoalaBear>, const N: usize, const H: usize>(
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
fn negacyclic_conv_n_recursive<R: Algebra<KoalaBear>, const N: usize, const H: usize>(
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
fn conv8<R: Algebra<KoalaBear>>(lhs: [R; 8], rhs: [KoalaBear; 8], output: &mut [R]) {
    conv_n_recursive(lhs, rhs, output, conv4::<R>, negacyclic_conv4::<R>);
}

#[inline(always)]
fn negacyclic_conv8<R: Algebra<KoalaBear>>(lhs: [R; 8], rhs: [KoalaBear; 8], output: &mut [R]) {
    negacyclic_conv_n_recursive(lhs, rhs, output, negacyclic_conv4::<R>);
}

/// Circulant MDS multiply via Karatsuba convolution: state = C * state.
#[inline(always)]
fn mds_karatsuba_16<R: Algebra<KoalaBear>>(state: &mut [R; 16]) {
    let input = *state;
    conv_n_recursive(
        input,
        MDS_CIRC_COL,
        state.as_mut_slice(),
        conv8::<R>,
        negacyclic_conv8::<R>,
    );
}

/// Public circulant MDS multiply.
#[inline(always)]
pub fn mds_circ_16<R: Algebra<KoalaBear>>(state: &mut [R; 16]) {
    mds_karatsuba_16(state);
}

// =========================================================================
// Sparse matrix decomposition helpers (for NEON partial rounds)
// =========================================================================

/// Expand a circulant matrix from its first column into a dense NxN matrix.
#[allow(dead_code)]
fn circulant_to_dense(first_col: &[KoalaBear; 16]) -> [[KoalaBear; 16]; 16] {
    core::array::from_fn(|i| core::array::from_fn(|j| first_col[(16 + i - j) % 16]))
}

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
    /// Eigenvalues of circulant MDS in bit-reversed order.
    lambda_br: [KoalaBear; 16],
    /// Forward-substituted scalar constants for partial rounds.
    textbook_scalar: [KoalaBear; POSEIDON1_PARTIAL_ROUNDS],
    /// Residual from forward constant substitution.
    textbook_residual: [KoalaBear; 16],

    // --- Sparse matrix decomposition for NEON fast path ---
    /// First round constant vector (full width), added once before m_i multiply.
    #[allow(dead_code)]
    sparse_first_round_constants: [KoalaBear; 16],
    /// Dense transition matrix m_i, applied once before the partial round loop.
    #[allow(dead_code)]
    sparse_m_i: [[KoalaBear; 16]; 16],
    /// Per-round full first row: [mds_0_0, ŵ[0], ..., ŵ[14]].
    /// Length = POSEIDON1_PARTIAL_ROUNDS.
    #[allow(dead_code)]
    sparse_first_row: Vec<[KoalaBear; 16]>,
    /// Per-round first-column vectors (excluding [0,0]).
    /// `v[r]` = [v[0], ..., v[14], 0]. Length = POSEIDON1_PARTIAL_ROUNDS.
    #[allow(dead_code)]
    sparse_v: Vec<[KoalaBear; 16]>,
    /// Scalar constants for partial rounds 0..RP-2.
    /// Length = POSEIDON1_PARTIAL_ROUNDS - 1.
    #[allow(dead_code)]
    sparse_round_constants: Vec<KoalaBear>,

    // --- NEON pre-packed constants ---
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    neon: NeonPrecomputed,
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
struct NeonPrecomputed {
    /// Initial full round constants in negative NEON form (only first 3 rounds;
    /// the 4th is fused with the partial round entry).
    packed_initial_rc: [[core::arch::aarch64::int32x4_t; 16]; POSEIDON1_HALF_FULL_ROUNDS - 1],
    /// Terminal full round constants in negative NEON form.
    packed_terminal_rc: [[core::arch::aarch64::int32x4_t; 16]; POSEIDON1_HALF_FULL_ROUNDS],
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
    /// Last initial round constant in negative NEON form (for fused add_rc_and_sbox).
    packed_last_initial_rc: [core::arch::aarch64::int32x4_t; 16],
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

impl Precomputed {
    #[allow(dead_code)]
    fn lambda_br(&self) -> &[KoalaBear; 16] {
        &self.lambda_br
    }
}

static PRECOMPUTED: OnceLock<Precomputed> = OnceLock::new();

fn precomputed() -> &'static Precomputed {
    PRECOMPUTED.get_or_init(|| {
        // Eigenvalues: IDFT_unnorm(col) in bit-reversed order.
        let mut lambda_br = MDS_CIRC_COL;
        dif_ifft_16_mut(&mut lambda_br);

        // Dense MDS for forward constant substitution.
        let mds: [[KoalaBear; 16]; 16] =
            core::array::from_fn(|i| core::array::from_fn(|j| MDS_CIRC_COL[(16 + i - j) % 16]));

        let partial_rc =
            &POSEIDON1_RC[POSEIDON1_HALF_FULL_ROUNDS..POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS];

        // --- Textbook (frequency-domain) constants ---
        let mut acc = [KoalaBear::ZERO; 16];
        let mut textbook_scalar = [KoalaBear::ZERO; POSEIDON1_PARTIAL_ROUNDS];
        for (k, rc) in partial_rc.iter().enumerate() {
            textbook_scalar[k] = rc[0] + acc[0];
            let remainder: [KoalaBear; 16] =
                core::array::from_fn(|i| if i == 0 { KoalaBear::ZERO } else { rc[i] + acc[i] });
            acc = core::array::from_fn(|i| {
                let mut s = KoalaBear::ZERO;
                for j in 0..16 {
                    s += mds[i][j] * remainder[j];
                }
                s
            });
        }

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
            use crate::convert_to_vec_neg_form_neon;

            let pack = |c: KoalaBear| PackedMontyField31Neon::<FP>::from(c);
            let neg_form = |c: KoalaBear| convert_to_vec_neg_form_neon::<FP>(c.value as i32);

            // Initial full round constants (only first 3; 4th is fused).
            let init_rc = poseidon1_initial_constants();
            let packed_initial_rc: [[core::arch::aarch64::int32x4_t; 16]; POSEIDON1_HALF_FULL_ROUNDS - 1] =
                core::array::from_fn(|r| init_rc[r].map(neg_form));

            // Last initial round constant (for fused add_rc_and_sbox before partial rounds).
            let packed_last_initial_rc = init_rc[POSEIDON1_HALF_FULL_ROUNDS - 1].map(neg_form);

            // Terminal full round constants.
            let term_rc = poseidon1_final_constants();
            let packed_terminal_rc: [[core::arch::aarch64::int32x4_t; 16]; POSEIDON1_HALF_FULL_ROUNDS] =
                core::array::from_fn(|r| term_rc[r].map(neg_form));

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
            let inv16 = KoalaBear::new(1997537281); // 16^{-1} mod p
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
            lambda_br,
            textbook_scalar,
            textbook_residual: acc,
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
        0x7ee56a48, 0x11367045, 0x12e41941, 0x7ebbc12b, 0x1970b7d5, 0x662b60e8, 0x3e4990c6, 0x679f91f5, 0x350813bb,
        0x00874ad4, 0x28a0081a, 0x18fa5872, 0x5f25b071, 0x5e5d5998, 0x5e6fd3e7, 0x5b2e2660,
    ],
    [
        0x6f1837bf, 0x3fe6182b, 0x1edd7ac5, 0x57470d00, 0x43d486d5, 0x1982c70f, 0x0ea53af9, 0x61d6165b, 0x51639c00,
        0x2dec352c, 0x2950e531, 0x2d2cb947, 0x08256cef, 0x1a0109f6, 0x1f51faf3, 0x5cef1c62,
    ],
    [
        0x3d65e50e, 0x33d91626, 0x133d5a1e, 0x0ff49b0d, 0x38900cd1, 0x2c22cc3f, 0x28852bb2, 0x06c65a02, 0x7b2cf7bc,
        0x68016e1a, 0x15e16bc0, 0x5248149a, 0x6dd212a0, 0x18d6830a, 0x5001be82, 0x64dac34e,
    ],
    [
        0x5902b287, 0x426583a0, 0x0c921632, 0x3fe028a5, 0x245f8e49, 0x43bb297e, 0x7873dbd9, 0x3cc987df, 0x286bb4ce,
        0x640a8dcd, 0x512a8e36, 0x03a4cf55, 0x481837a2, 0x03d6da84, 0x73726ac7, 0x760e7fdf,
    ],
    // Partial rounds (20)
    [
        0x54dfeb5d, 0x7d40afd6, 0x722cb316, 0x106a4573, 0x45a7ccdb, 0x44061375, 0x154077a5, 0x45744faa, 0x4eb5e5ee,
        0x3794e83f, 0x47c7093c, 0x5694903c, 0x69cb6299, 0x373df84c, 0x46a0df58, 0x46b8758a,
    ],
    [
        0x3241ebcb, 0x0b09d233, 0x1af42357, 0x1e66cec2, 0x43e7dc24, 0x259a5d61, 0x27e85a3b, 0x1b9133fa, 0x343e5628,
        0x485cd4c2, 0x16e269f5, 0x165b60c6, 0x25f683d9, 0x124f81f9, 0x174331f9, 0x77344dc5,
    ],
    [
        0x5a821dba, 0x5fc4177f, 0x54153bf5, 0x5e3f1194, 0x3bdbf191, 0x088c84a3, 0x68256c9b, 0x3c90bbc6, 0x6846166a,
        0x03f4238d, 0x463335fb, 0x5e3d3551, 0x6e59ae6f, 0x32d06cc0, 0x596293f3, 0x6c87edb2,
    ],
    [
        0x08fc60b5, 0x34bcca80, 0x24f007f3, 0x62731c6f, 0x1e1db6c6, 0x0ca409bb, 0x585c1e78, 0x56e94edc, 0x16d22734,
        0x18e11467, 0x7b2c3730, 0x770075e4, 0x35d1b18c, 0x22be3db5, 0x4fb1fbb7, 0x477cb3ed,
    ],
    [
        0x7d5311c6, 0x5b62ae7d, 0x559c5fa8, 0x77f15048, 0x3211570b, 0x490fef6a, 0x77ec311f, 0x2247171b, 0x4e0ac711,
        0x2edf69c9, 0x3b5a8850, 0x65809421, 0x5619b4aa, 0x362019a7, 0x6bf9d4ed, 0x5b413dff,
    ],
    [
        0x617e181e, 0x5e7ab57b, 0x33ad7833, 0x3466c7ca, 0x6488dff4, 0x71f068f4, 0x056e891f, 0x04f1eccc, 0x663257d5,
        0x671e31b9, 0x5871987c, 0x280c109e, 0x2a227761, 0x350a25e9, 0x5b91b1c4, 0x7a073546,
    ],
    [
        0x01826270, 0x53a67720, 0x0ed4b074, 0x34cf0c4e, 0x6e751e88, 0x29bd5f59, 0x49ec32df, 0x7693452b, 0x3cf09e58,
        0x6ba0e2bf, 0x7ab93acf, 0x3ce597df, 0x536e3d42, 0x147a808d, 0x5e32eb56, 0x5a203323,
    ],
    [
        0x50965766, 0x6d44b7c5, 0x6698636a, 0x57b84f9f, 0x554b61b9, 0x6da0ab28, 0x1585b6ac, 0x6705a2b4, 0x152872f6,
        0x0f4409fd, 0x23a9dd60, 0x6f2b18d4, 0x65ac9fd4, 0x2f0efbea, 0x591e67fd, 0x217ca19b,
    ],
    [
        0x469c90ca, 0x03d60ef5, 0x4ea7857e, 0x07c86a4f, 0x288ed461, 0x2fe51b22, 0x7e293614, 0x2c4beb85, 0x5b0b7d11,
        0x1e17dff6, 0x089beae1, 0x0a5acf1a, 0x2fc33d8f, 0x60422dc6, 0x6e1dc939, 0x635351b9,
    ],
    [
        0x55522fc0, 0x3eb94ef7, 0x2a24a65c, 0x2e139c76, 0x51391144, 0x78cc0742, 0x579538f9, 0x44de9aae, 0x3c2f1e2e,
        0x195747be, 0x2496339c, 0x650b2e39, 0x52899665, 0x6cb35558, 0x0f461c1c, 0x70f6b270,
    ],
    [
        0x3faaa36f, 0x62e3348a, 0x672167cb, 0x394c880b, 0x2a46ba82, 0x63ffb74a, 0x1cf875d6, 0x53d12772, 0x036a4552,
        0x3bdd9f2b, 0x02f72c24, 0x02b6006c, 0x077fe158, 0x1f9d6ea4, 0x20904d6f, 0x5d6534fa,
    ],
    [
        0x066d8974, 0x6198f1f4, 0x26301ab4, 0x41f274c2, 0x00eac15c, 0x28b54b47, 0x2339739d, 0x48c6281c, 0x4ed935fc,
        0x3f9187fa, 0x4a1930a6, 0x3ad4d736, 0x0f3f1889, 0x635a388f, 0x2862c145, 0x277ed1e8,
    ],
    [
        0x4db23cad, 0x1f1b11f5, 0x1f3dba2b, 0x1c26eb4e, 0x0f7f5546, 0x6cd024b0, 0x67c47902, 0x793b8900, 0x0e8a283c,
        0x4590b7ea, 0x6f567a2b, 0x5dc97300, 0x15247bc6, 0x50567fcb, 0x133eff84, 0x547dc2ef,
    ],
    [
        0x34eb3dbb, 0x12402317, 0x66c6ae49, 0x174338b6, 0x24251008, 0x1b514927, 0x062d98d6, 0x7af30bbc, 0x26af15e8,
        0x70d907a3, 0x5dfc5cac, 0x731f27ec, 0x53aa7d3f, 0x63ab0ec6, 0x216053f4, 0x18796b39,
    ],
    [
        0x19156afd, 0x5eea6973, 0x6704c6a9, 0x0dce002b, 0x331169c0, 0x714d7178, 0x3ddaffaf, 0x7e464957, 0x20ca59ea,
        0x679820c9, 0x42ef21a1, 0x798ea089, 0x14a74fa3, 0x0c06cf18, 0x6a4c8d52, 0x620f6d81,
    ],
    [
        0x2220901a, 0x5277bb90, 0x230bf95e, 0x0ad8847a, 0x5e96e8b6, 0x77b4056e, 0x70a50d2c, 0x5f0eed59, 0x3646c4df,
        0x10eb9a87, 0x21eed6b7, 0x534add36, 0x6e3e7421, 0x2b25810e, 0x1d8f707b, 0x45318a1a,
    ],
    [
        0x677f8ff2, 0x0258c9e0, 0x4cd02a00, 0x2e24ff15, 0x634a715d, 0x4ac01e59, 0x601511e1, 0x26e9c01a, 0x4c165c6e,
        0x57cd1140, 0x3ac6543b, 0x6787d847, 0x037dfbf9, 0x6dd9d079, 0x4d24b281, 0x2a6f407d,
    ],
    [
        0x0131df8e, 0x4b8a7896, 0x23700858, 0x2cf5e534, 0x12aafc3f, 0x54568d03, 0x1a250735, 0x5331686d, 0x4ce76d91,
        0x799c1a8c, 0x2b7a8ac9, 0x60aee672, 0x74f7421c, 0x3c42146d, 0x26d369c5, 0x4ae54a12,
    ],
    [
        0x7eea16d1, 0x5ce3eae8, 0x69f28994, 0x262b8642, 0x610d4cc4, 0x5e1af21c, 0x1a8526d0, 0x316b127b, 0x3576fe5d,
        0x02d968a0, 0x4ba00f51, 0x40bed993, 0x377fb907, 0x7859216e, 0x1931d9d1, 0x53b0934e,
    ],
    [
        0x71914ff7, 0x4eabae6c, 0x7196468e, 0x164b3cc2, 0x58cb66c0, 0x4c147307, 0x6b3afccd, 0x4236518b, 0x4ad85605,
        0x291382e1, 0x1e89b6cf, 0x5e16c3a8, 0x2e675921, 0x24300954, 0x05e555c3, 0x78880a24,
    ],
    // Terminal full rounds (4)
    [
        0x763a3125, 0x4f53b240, 0x18b7fa43, 0x2bbe8a73, 0x1c9a12f2, 0x3f6fd40d, 0x0e1d4ec4, 0x1361c64d, 0x09a8f470,
        0x03d23a40, 0x109ad290, 0x28c2fb88, 0x3b6498f2, 0x74d8be57, 0x6a4277d2, 0x18c2b3d4,
    ],
    [
        0x6252c30c, 0x07cc2560, 0x209fe15b, 0x52a55fac, 0x4df19eb7, 0x02521116, 0x5e414ff1, 0x3cd9a1f4, 0x005aad15,
        0x27a53f00, 0x72bbe9cb, 0x71d8bd7d, 0x4194b79a, 0x48e87a72, 0x3341553c, 0x63d34faa,
    ],
    [
        0x132a01e3, 0x3833e2d9, 0x49726e04, 0x054957f8, 0x7b71bce4, 0x73eec57d, 0x556e5533, 0x1fa93fde, 0x346a8ca8,
        0x1162dfde, 0x5c30d028, 0x094a4294, 0x3052dcda, 0x37988498, 0x51f06b97, 0x65848779,
    ],
    [
        0x7599b0d4, 0x436fdabc, 0x66c5b77d, 0x40c86a9e, 0x27e7055b, 0x6d0dd9d8, 0x7e5598b5, 0x1a4d04f3, 0x5e3b2bc7,
        0x533b5b2f, 0x3e33a125, 0x664d71ce, 0x382e6c2a, 0x24c4eb6e, 0x13f246f7, 0x07e2d7ef,
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
        let lambda = &self.pre.lambda_br;

        // Initial full rounds (all but last).
        for rc in &poseidon1_initial_constants()[..POSEIDON1_HALF_FULL_ROUNDS - 1] {
            Self::full_round(state, rc);
        }

        // Last initial full round: AddRC + S-box, then enter frequency domain
        // (fuses the last MDS with the frequency-domain entry, saving one FFT pair).
        let rc_last = &poseidon1_initial_constants()[POSEIDON1_HALF_FULL_ROUNDS - 1];
        for (s, &c) in state.iter_mut().zip(rc_last.iter()) {
            *s += c;
        }
        for s in state.iter_mut() {
            *s = s.injective_exp_n();
        }

        // --- Partial rounds in frequency domain ---
        //
        // The circulant MDS is diagonal in IDFT domain: multiply by eigenvalues.
        // With forward constant substitution, each partial round reduces to:
        //   state[0] += scalar, state[0] = state[0]^3, state = MDS * state.
        // In frequency domain: add scalar to all bins, apply eigenvalues.
        // s0 = sum(f_br) / 16  (always a simple sum of IDFT coefficients).
        {
            let tb_scalar = &self.pre.textbook_scalar;
            let tb_residual = &self.pre.textbook_residual;

            let mut f_br = *state;
            dif_ifft_16_mut(&mut f_br);

            // Apply MDS of last initial full round.
            for j in 0..16 {
                f_br[j] *= lambda[j];
            }
            let mut s0 = f_br[0];
            for j in 1..16 {
                s0 += f_br[j];
            }
            s0 = s0.div_2exp_u64(4);

            for k in 0..POSEIDON1_PARTIAL_ROUNDS {
                let s0_prime = s0 + tb_scalar[k];
                let cube = s0_prime.injective_exp_n();
                let update = cube - s0;

                for j in 0..16 {
                    f_br[j] += update;
                }
                for j in 0..16 {
                    f_br[j] *= lambda[j];
                }

                s0 = f_br[0];
                for j in 1..16 {
                    s0 += f_br[j];
                }
                s0 = s0.div_2exp_u64(4);
            }

            // Return to time domain.
            dit_fft_16_mut(&mut f_br);
            for j in 0..16 {
                state[j] = f_br[j].div_2exp_u64(4);
            }
            // Add residual from forward constant substitution.
            for j in 0..16 {
                state[j] += tb_residual[j];
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
        mds_karatsuba_16(state);
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
                    let s0_signed = split.s0.to_signed_vector();
                    let s0_sboxed = exp_small::<FP, 3>(s0_signed);
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
