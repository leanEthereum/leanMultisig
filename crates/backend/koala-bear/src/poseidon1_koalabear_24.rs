// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::sync::OnceLock;

use crate::KoalaBear;
use crate::symmetric::Permutation;
use field::{Algebra, Field, InjectiveMonomial, PrimeCharacteristicRing};

pub const POSEIDON1_WIDTH_24: usize = 24;
pub const POSEIDON1_HALF_FULL_ROUNDS_24: usize = 4;
pub const POSEIDON1_PARTIAL_ROUNDS_24: usize = 23;
pub const POSEIDON1_SBOX_DEGREE_24: u64 = 3;
const POSEIDON1_N_ROUNDS_24: usize = 2 * POSEIDON1_HALF_FULL_ROUNDS_24 + POSEIDON1_PARTIAL_ROUNDS_24;

// =========================================================================
// MDS circulant matrix (first column)
// =========================================================================

/// First column of the circulant MDS matrix for width 24.
///
/// Derived from the plonky3 first-row data via first_row_to_first_col:
/// col[0] = row[0], col[i] = row[24 - i] for i = 1..23.
const MDS_CIRC_COL_24: [KoalaBear; 24] = KoalaBear::new_array([
    0x2D0AAAAB, 0x0878A07F, 0x17E118F6, 0x5C7790FA, 0x0A6E572C, 0x6BE4DF69, 0x0524C7F2, 0x0C23DC41, 0x3C2C3DBE,
    0x1689DD98, 0x5D57AFC2, 0x2495A71D, 0x68FC71C8, 0x0360405D, 0x26D52A61, 0x3C0F5038, 0x77CDA9E2, 0x729601A7,
    0x18D6F3CA, 0x60703026, 0x6D91A8D5, 0x04ECBEB5, 0x17F5551D, 0x64850517,
]);

// =========================================================================
// Karatsuba convolution chain: 3 → 6 → 12 → 24
//
// Ported from Plonky3 mds/src/karatsuba_convolution.rs (FieldConvolve).
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
fn conv3<R: Algebra<KoalaBear>>(lhs: [R; 3], rhs: [KoalaBear; 3], output: &mut [R]) {
    output[0] = parity_dot(lhs, [rhs[0], rhs[2], rhs[1]]);
    output[1] = parity_dot(lhs, [rhs[1], rhs[0], rhs[2]]);
    output[2] = parity_dot(lhs, [rhs[2], rhs[1], rhs[0]]);
}

#[inline(always)]
fn negacyclic_conv3<R: Algebra<KoalaBear>>(lhs: [R; 3], rhs: [KoalaBear; 3], output: &mut [R]) {
    output[0] = parity_dot(lhs, [rhs[0], -rhs[2], -rhs[1]]);
    output[1] = parity_dot(lhs, [rhs[1], rhs[0], -rhs[2]]);
    output[2] = parity_dot(lhs, [rhs[2], rhs[1], rhs[0]]);
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
fn conv6<R: Algebra<KoalaBear>>(lhs: [R; 6], rhs: [KoalaBear; 6], output: &mut [R]) {
    conv_n_recursive(lhs, rhs, output, conv3::<R>, negacyclic_conv3::<R>);
}

#[inline(always)]
fn negacyclic_conv6<R: Algebra<KoalaBear>>(lhs: [R; 6], rhs: [KoalaBear; 6], output: &mut [R]) {
    negacyclic_conv_n_recursive(lhs, rhs, output, negacyclic_conv3::<R>);
}

#[inline(always)]
fn conv12<R: Algebra<KoalaBear>>(lhs: [R; 12], rhs: [KoalaBear; 12], output: &mut [R]) {
    conv_n_recursive(lhs, rhs, output, conv6::<R>, negacyclic_conv6::<R>);
}

#[inline(always)]
fn negacyclic_conv12<R: Algebra<KoalaBear>>(lhs: [R; 12], rhs: [KoalaBear; 12], output: &mut [R]) {
    negacyclic_conv_n_recursive(lhs, rhs, output, negacyclic_conv6::<R>);
}

/// Circulant MDS multiply via Karatsuba convolution: state = C * state.
#[inline(always)]
fn mds_karatsuba_24<R: Algebra<KoalaBear>>(state: &mut [R; 24]) {
    let input = *state;
    conv_n_recursive(
        input,
        MDS_CIRC_COL_24,
        state.as_mut_slice(),
        conv12::<R>,
        negacyclic_conv12::<R>,
    );
}

/// Public circulant MDS multiply.
#[inline(always)]
pub fn mds_circ_24<R: Algebra<KoalaBear>>(state: &mut [R; 24]) {
    mds_karatsuba_24(state);
}

// =========================================================================
// NEON-optimized Karatsuba using mixed_dot_product (fewer Montgomery reductions)
//
// On NEON, mixed_dot_product accumulates products in 64-bit precision and
// does a single Montgomery reduction. The rhs (MDS column) stays as scalar
// KoalaBear values throughout the recursion, avoiding redundant NEON
// add/sub operations and SIMD port contention. Only at the leaf level
// are scalars broadcast to NEON lanes for the multiply-accumulate.
// =========================================================================

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
mod neon_karatsuba {
    use super::*;
    type P = PackedKB;
    type F = KoalaBear;

    #[inline(always)]
    fn pdot<const N: usize>(lhs: [P; N], rhs: [F; N]) -> P {
        P::mixed_dot_product(&lhs, &rhs)
    }

    #[inline(always)]
    fn conv3(lhs: [P; 3], rhs: [F; 3], output: &mut [P]) {
        output[0] = pdot(lhs, [rhs[0], rhs[2], rhs[1]]);
        output[1] = pdot(lhs, [rhs[1], rhs[0], rhs[2]]);
        output[2] = pdot(lhs, [rhs[2], rhs[1], rhs[0]]);
    }

    #[inline(always)]
    fn negacyclic_conv3(lhs: [P; 3], rhs: [F; 3], output: &mut [P]) {
        output[0] = pdot(lhs, [rhs[0], -rhs[2], -rhs[1]]);
        output[1] = pdot(lhs, [rhs[1], rhs[0], -rhs[2]]);
        output[2] = pdot(lhs, [rhs[2], rhs[1], rhs[0]]);
    }

    #[inline(always)]
    fn conv_n<const N: usize, const H: usize>(
        lhs: [P; N],
        rhs: [F; N],
        output: &mut [P],
        inner_conv: fn([P; H], [F; H], &mut [P]),
        inner_neg: fn([P; H], [F; H], &mut [P]),
    ) {
        let mut lp = [P::ZERO; H];
        let mut ln = [P::ZERO; H];
        let mut rp = [F::ZERO; H];
        let mut rn = [F::ZERO; H];
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
    fn negacyclic_conv_n<const N: usize, const H: usize>(
        lhs: [P; N],
        rhs: [F; N],
        output: &mut [P],
        inner_neg: fn([P; H], [F; H], &mut [P]),
    ) {
        let mut le = [P::ZERO; H];
        let mut lo = [P::ZERO; H];
        let mut ls = [P::ZERO; H];
        let mut re = [F::ZERO; H];
        let mut ro = [F::ZERO; H];
        let mut rs = [F::ZERO; H];
        for i in 0..H {
            le[i] = lhs[2 * i];
            lo[i] = lhs[2 * i + 1];
            ls[i] = le[i] + lo[i];
            re[i] = rhs[2 * i];
            ro[i] = rhs[2 * i + 1];
            rs[i] = re[i] + ro[i];
        }
        let mut es = [P::ZERO; H];
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
    fn conv6(lhs: [P; 6], rhs: [F; 6], output: &mut [P]) {
        conv_n(lhs, rhs, output, conv3, negacyclic_conv3);
    }

    #[inline(always)]
    fn negacyclic_conv6(lhs: [P; 6], rhs: [F; 6], output: &mut [P]) {
        negacyclic_conv_n(lhs, rhs, output, negacyclic_conv3);
    }

    #[inline(always)]
    fn conv12(lhs: [P; 12], rhs: [F; 12], output: &mut [P]) {
        conv_n(lhs, rhs, output, conv6, negacyclic_conv6);
    }

    #[inline(always)]
    fn negacyclic_conv12(lhs: [P; 12], rhs: [F; 12], output: &mut [P]) {
        negacyclic_conv_n(lhs, rhs, output, negacyclic_conv6);
    }

    #[inline(always)]
    pub(super) fn mds_karatsuba_24_neon(state: &mut [P; 24], col: &[F; 24]) {
        let input = *state;
        conv_n(input, *col, state.as_mut_slice(), conv12, negacyclic_conv12);
    }
}

// =========================================================================
// Sparse matrix decomposition helpers (precomputation only)
// =========================================================================

type F24 = [KoalaBear; 24];
type M24 = [[KoalaBear; 24]; 24];

fn matrix_mul_24(a: &M24, b: &M24) -> M24 {
    core::array::from_fn(|i| {
        core::array::from_fn(|j| {
            let mut s = KoalaBear::ZERO;
            for k in 0..24 {
                s += a[i][k] * b[k][j];
            }
            s
        })
    })
}

fn matrix_vec_mul_24(m: &M24, v: &F24) -> F24 {
    core::array::from_fn(|i| {
        let mut s = KoalaBear::ZERO;
        for j in 0..24 {
            s += m[i][j] * v[j];
        }
        s
    })
}

fn matrix_transpose_24(m: &M24) -> M24 {
    core::array::from_fn(|i| core::array::from_fn(|j| m[j][i]))
}

fn matrix_inverse_24(m: &M24) -> M24 {
    let mut aug: M24 = *m;
    let mut inv: M24 =
        core::array::from_fn(|i| core::array::from_fn(|j| if i == j { KoalaBear::ONE } else { KoalaBear::ZERO }));
    for col in 0..24 {
        let pivot_row = (col..24)
            .find(|&r| aug[r][col] != KoalaBear::ZERO)
            .expect("Matrix is singular");
        if pivot_row != col {
            aug.swap(col, pivot_row);
            inv.swap(col, pivot_row);
        }
        let pivot_inv = aug[col][col].inverse();
        for j in 0..24 {
            aug[col][j] *= pivot_inv;
            inv[col][j] *= pivot_inv;
        }
        for i in 0..24 {
            if i == col {
                continue;
            }
            let factor = aug[i][col];
            if factor == KoalaBear::ZERO {
                continue;
            }
            let aug_col_row = aug[col];
            let inv_col_row = inv[col];
            for j in 0..24 {
                aug[i][j] -= factor * aug_col_row[j];
                inv[i][j] -= factor * inv_col_row[j];
            }
        }
    }
    inv
}

/// Inverse of the 23x23 bottom-right submatrix (Vec-based).
fn submatrix_inverse_23(m: &M24) -> Vec<Vec<KoalaBear>> {
    let n = 23;
    let mut sub: Vec<Vec<KoalaBear>> = (0..n).map(|i| (0..n).map(|j| m[i + 1][j + 1]).collect()).collect();
    let mut inv: Vec<Vec<KoalaBear>> = (0..n)
        .map(|i| {
            let mut row = vec![KoalaBear::ZERO; n];
            row[i] = KoalaBear::ONE;
            row
        })
        .collect();
    for col in 0..n {
        let pivot_row = (col..n)
            .find(|&r| sub[r][col] != KoalaBear::ZERO)
            .expect("Submatrix is singular");
        if pivot_row != col {
            sub.swap(col, pivot_row);
            inv.swap(col, pivot_row);
        }
        let pivot_inv = sub[col][col].inverse();
        for j in 0..n {
            sub[col][j] *= pivot_inv;
            inv[col][j] *= pivot_inv;
        }
        for i in 0..n {
            if i == col {
                continue;
            }
            let factor = sub[i][col];
            if factor == KoalaBear::ZERO {
                continue;
            }
            let sub_col_row: Vec<KoalaBear> = sub[col].clone();
            let inv_col_row: Vec<KoalaBear> = inv[col].clone();
            for j in 0..n {
                sub[i][j] -= factor * sub_col_row[j];
                inv[i][j] -= factor * inv_col_row[j];
            }
        }
    }
    inv
}

/// Factor the dense MDS matrix into sparse matrices for partial rounds.
/// Returns (m_i, v_collection, w_hat_collection) in forward application order.
fn compute_equivalent_matrices_24(mds: &M24) -> (M24, Vec<F24>, Vec<F24>) {
    let rounds_p = POSEIDON1_PARTIAL_ROUNDS_24;
    let mut w_hat_collection: Vec<F24> = Vec::with_capacity(rounds_p);
    let mut v_collection: Vec<F24> = Vec::with_capacity(rounds_p);

    let mds_t = matrix_transpose_24(mds);
    let mut m_mul = mds_t;
    let mut m_i = [[KoalaBear::ZERO; 24]; 24];

    for _ in 0..rounds_p {
        let v_arr: F24 = core::array::from_fn(|j| if j < 23 { m_mul[0][j + 1] } else { KoalaBear::ZERO });
        let w: Vec<KoalaBear> = (1..24).map(|i| m_mul[i][0]).collect();
        let m_hat_inv = submatrix_inverse_23(&m_mul);
        let w_hat_arr: F24 = core::array::from_fn(|i| {
            if i < 23 {
                let mut s = KoalaBear::ZERO;
                for k in 0..23 {
                    s += m_hat_inv[i][k] * w[k];
                }
                s
            } else {
                KoalaBear::ZERO
            }
        });
        v_collection.push(v_arr);
        w_hat_collection.push(w_hat_arr);

        m_i = m_mul;
        m_i[0][0] = KoalaBear::ONE;
        for row in m_i.iter_mut().skip(1) {
            row[0] = KoalaBear::ZERO;
        }
        for elem in m_i[0].iter_mut().skip(1) {
            *elem = KoalaBear::ZERO;
        }
        m_mul = matrix_mul_24(&mds_t, &m_i);
    }

    let m_i_returned = matrix_transpose_24(&m_i);
    v_collection.reverse();
    w_hat_collection.reverse();
    (m_i_returned, v_collection, w_hat_collection)
}

/// Compress round constants via backward substitution through MDS^{-1}.
fn equivalent_round_constants_24(partial_rc: &[F24], mds_inv: &M24) -> (F24, Vec<KoalaBear>) {
    let rounds_p = partial_rc.len();
    let mut opt_partial_rc = vec![KoalaBear::ZERO; rounds_p];
    let mut tmp = partial_rc[rounds_p - 1];
    for i in (0..rounds_p - 1).rev() {
        let inv_cip = matrix_vec_mul_24(mds_inv, &tmp);
        opt_partial_rc[i + 1] = inv_cip[0];
        tmp = partial_rc[i];
        for j in 1..24 {
            tmp[j] += inv_cip[j];
        }
    }
    let first_round_constants = tmp;
    let scalar_constants = opt_partial_rc[1..].to_vec();
    (first_round_constants, scalar_constants)
}

// =========================================================================
// NEON types (conditional)
// =========================================================================

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
type FP = crate::KoalaBearParameters;
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
type PackedKB = crate::PackedKoalaBearNeon;

// =========================================================================
// Precomputed constants
// =========================================================================

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
struct NeonPrecomputed24 {
    /// Initial full round constants in negative NEON form (first 3 rounds).
    packed_initial_rc: [[core::arch::aarch64::int32x4_t; 24]; POSEIDON1_HALF_FULL_ROUNDS_24 - 1],
    /// Last initial round constant in negative NEON form.
    packed_last_initial_rc: [core::arch::aarch64::int32x4_t; 24],
    /// Terminal full round constants in negative NEON form.
    packed_terminal_rc: [[core::arch::aarch64::int32x4_t; 24]; POSEIDON1_HALF_FULL_ROUNDS_24],
    /// MDS circulant column for NEON Karatsuba (scalar, not packed).
    /// Kept as scalar so the Karatsuba recursion avoids redundant NEON
    /// operations on the constant side, reducing SIMD port contention.
    mds_col: [KoalaBear; 24],
    /// Fused matrix: m_i * MDS.
    packed_fused_mi_mds: [[PackedKB; 24]; 24],
    /// Fused bias: m_i * first_round_constants.
    packed_fused_bias: [PackedKB; 24],
    /// Pre-packed sparse first rows.
    packed_sparse_first_row: [[PackedKB; 24]; POSEIDON1_PARTIAL_ROUNDS_24],
    /// Pre-packed v vectors.
    packed_sparse_v: [[PackedKB; 24]; POSEIDON1_PARTIAL_ROUNDS_24],
    /// Pre-packed scalar round constants for partial rounds 0..RP-2.
    packed_round_constants: [PackedKB; POSEIDON1_PARTIAL_ROUNDS_24 - 1],
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl std::fmt::Debug for NeonPrecomputed24 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NeonPrecomputed24").finish_non_exhaustive()
    }
}

#[derive(Debug)]
struct Precomputed24 {
    /// First round constant vector (full width), added once before m_i multiply.
    sparse_first_round_constants: F24,
    /// Dense transition matrix m_i, applied once before the partial round loop.
    sparse_m_i: M24,
    /// Per-round full first row: [mds_0_0, ŵ[0], ..., ŵ[22]].
    sparse_first_row: Vec<F24>,
    /// Per-round first-column vectors (excluding [0,0]).
    sparse_v: Vec<F24>,
    /// Scalar constants for partial rounds 0..RP-2.
    sparse_round_constants: Vec<KoalaBear>,

    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    neon: NeonPrecomputed24,
}

static PRECOMPUTED_24: OnceLock<Precomputed24> = OnceLock::new();

fn precomputed_24() -> &'static Precomputed24 {
    PRECOMPUTED_24.get_or_init(|| {
        let mds: M24 = core::array::from_fn(|i| core::array::from_fn(|j| MDS_CIRC_COL_24[(24 + i - j) % 24]));

        let partial_rc = &POSEIDON1_RC_24
            [POSEIDON1_HALF_FULL_ROUNDS_24..POSEIDON1_HALF_FULL_ROUNDS_24 + POSEIDON1_PARTIAL_ROUNDS_24];

        // Sparse matrix decomposition.
        let mds_inv = matrix_inverse_24(&mds);
        let (first_round_constants, scalar_round_constants) = equivalent_round_constants_24(partial_rc, &mds_inv);
        let (m_i, sparse_v, sparse_w_hat) = compute_equivalent_matrices_24(&mds);

        // Pre-assemble full first rows: [mds_0_0, ŵ[0], ..., ŵ[22]].
        let mds_0_0 = mds[0][0];
        let sparse_first_row: Vec<F24> = sparse_w_hat
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

            // Initial full round constants (first 3; 4th is fused).
            let init_rc = poseidon1_24_initial_constants();
            let packed_initial_rc: [[core::arch::aarch64::int32x4_t; 24]; POSEIDON1_HALF_FULL_ROUNDS_24 - 1] =
                core::array::from_fn(|r| init_rc[r].map(neg_form));
            let packed_last_initial_rc = init_rc[POSEIDON1_HALF_FULL_ROUNDS_24 - 1].map(neg_form);

            // Terminal full round constants.
            let term_rc = poseidon1_24_final_constants();
            let packed_terminal_rc: [[core::arch::aarch64::int32x4_t; 24]; POSEIDON1_HALF_FULL_ROUNDS_24] =
                core::array::from_fn(|r| term_rc[r].map(neg_form));

            // Pre-packed sparse constants.
            let packed_sparse_first_row: [[PackedKB; 24]; POSEIDON1_PARTIAL_ROUNDS_24] =
                core::array::from_fn(|r| sparse_first_row[r].map(pack));
            let packed_sparse_v: [[PackedKB; 24]; POSEIDON1_PARTIAL_ROUNDS_24] =
                core::array::from_fn(|r| sparse_v[r].map(pack));
            let packed_round_constants: [PackedKB; POSEIDON1_PARTIAL_ROUNDS_24 - 1] =
                core::array::from_fn(|r| pack(scalar_round_constants[r]));

            // MDS column for NEON Karatsuba (scalar, not packed).
            let mds_col: [KoalaBear; 24] = MDS_CIRC_COL_24;

            // Fused matrix: m_i * MDS.
            let fused_mi_mds = matrix_mul_24(&m_i, &mds);
            let packed_fused_mi_mds: [[PackedKB; 24]; 24] = core::array::from_fn(|i| fused_mi_mds[i].map(pack));

            // Fused bias: m_i * first_round_constants.
            let fused_bias = matrix_vec_mul_24(&m_i, &first_round_constants);
            let packed_fused_bias: [PackedKB; 24] = fused_bias.map(pack);

            NeonPrecomputed24 {
                packed_initial_rc,
                packed_last_initial_rc,
                packed_terminal_rc,
                mds_col,
                packed_fused_mi_mds,
                packed_fused_bias,
                packed_sparse_first_row,
                packed_sparse_v,
                packed_round_constants,
            }
        };

        Precomputed24 {
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

const POSEIDON1_RC_24: [[KoalaBear; 24]; POSEIDON1_N_ROUNDS_24] = KoalaBear::new_2d_array([
    // Initial full rounds (4)
    [
        0x1d0939dc, 0x6d050f8d, 0x628058ad, 0x2681385d, 0x3e3c62be, 0x032cfad8, 0x5a91ba3c, 0x015a56e6, 0x696b889c,
        0x0dbcd780, 0x5881b5c9, 0x2a076f2e, 0x55393055, 0x6513a085, 0x547ac78f, 0x4281c5b8, 0x3e7a3f6c, 0x34562c19,
        0x2c04e679, 0x0ed78234, 0x5f7a1aa9, 0x0177640e, 0x0ea4f8d1, 0x15be7692,
    ],
    [
        0x6eafdd62, 0x71a572c6, 0x72416f0a, 0x31ce1ad3, 0x2136a0cf, 0x1507c0eb, 0x1eb6e07a, 0x3a0ccf7b, 0x38e4bf31,
        0x44128286, 0x6b05e976, 0x244a9b92, 0x6e4b32a8, 0x78ee2496, 0x4761115b, 0x3d3a7077, 0x75d3c670, 0x396a2475,
        0x26dd00b4, 0x7df50f59, 0x0cb922df, 0x0568b190, 0x5bd3fcd6, 0x1351f58e,
    ],
    [
        0x52191b5f, 0x119171b8, 0x1e8bb727, 0x27d21f26, 0x36146613, 0x1ee817a2, 0x71abe84e, 0x44b88070, 0x5dc04410,
        0x2aeaa2f6, 0x2b7bb311, 0x6906884d, 0x0522e053, 0x0c45a214, 0x1b016998, 0x479b1052, 0x3acc89be, 0x0776021a,
        0x7a34a1f5, 0x70f87911, 0x2caf9d9e, 0x026aff1b, 0x2c42468e, 0x67726b45,
    ],
    [
        0x09b6f53c, 0x73d76589, 0x5793eeb0, 0x29e720f3, 0x75fc8bdf, 0x4c2fae0e, 0x20b41db3, 0x7e491510, 0x2cadef18,
        0x57fc24d6, 0x4d1ade4a, 0x36bf8e3c, 0x3511b63c, 0x64d8476f, 0x732ba706, 0x46634978, 0x0521c17c, 0x5ee69212,
        0x3559cba9, 0x2b33df89, 0x653538d6, 0x5fde8344, 0x4091605d, 0x2933bdde,
    ],
    // Partial rounds (23)
    [
        0x1395d4ca, 0x5dbac049, 0x51fc2727, 0x13407399, 0x39ac6953, 0x45e8726c, 0x75a7311c, 0x599f82c9, 0x702cf13b,
        0x026b8955, 0x44e09bbc, 0x2211207f, 0x5128b4e3, 0x591c41af, 0x674f5c68, 0x3981d0d3, 0x2d82f898, 0x707cd267,
        0x3b4cca45, 0x2ad0dc3c, 0x0cb79b37, 0x23f2f4e8, 0x3de4e739, 0x7d232359,
    ],
    [
        0x389d82f9, 0x259b2e6c, 0x45a94def, 0x0d497380, 0x5b049135, 0x3c268399, 0x78feb2f9, 0x300a3eec, 0x505165bb,
        0x20300973, 0x2327c081, 0x1a45a2f4, 0x5b32ea2e, 0x2d5d1a70, 0x053e613e, 0x5433e39f, 0x495529f0, 0x1eaa1aa9,
        0x578f572a, 0x698ede71, 0x5a0f9dba, 0x398a2e96, 0x0c7b2925, 0x2e6b9564,
    ],
    [
        0x026b00de, 0x7644c1e9, 0x5c23d0bd, 0x3470b5ef, 0x6013cf3a, 0x48747288, 0x13b7a543, 0x3eaebd44, 0x0004e60c,
        0x1e8363a2, 0x2343259a, 0x69da0c2a, 0x06e3e4c4, 0x1095018e, 0x0deea348, 0x1f4c5513, 0x4f9a3a98, 0x3179112b,
        0x524abb1f, 0x21615ba2, 0x23ab4065, 0x1202a1d1, 0x21d25b83, 0x6ed17c2f,
    ],
    [
        0x391e6b09, 0x5e4ed894, 0x6a2f58f2, 0x5d980d70, 0x3fa48c5e, 0x1f6366f7, 0x63540f5f, 0x6a8235ed, 0x14c12a78,
        0x6edde1c9, 0x58ce1c22, 0x718588bb, 0x334313ad, 0x7478dbc7, 0x647ad52f, 0x39e82049, 0x6fee146a, 0x082c2f24,
        0x1f093015, 0x30173c18, 0x53f70c0d, 0x6028ab0c, 0x2f47a1ee, 0x26a6780e,
    ],
    [
        0x3540bc83, 0x1812b49f, 0x5149c827, 0x631dd925, 0x001f2dea, 0x7dc05194, 0x3789672e, 0x7cabf72e, 0x242dbe2f,
        0x0b07a51d, 0x38653650, 0x50785c4e, 0x60e8a7e0, 0x07464338, 0x3482d6e1, 0x08a69f1e, 0x3f2aff24, 0x5814c30d,
        0x13fecab2, 0x61cb291a, 0x68c8226f, 0x5c757eea, 0x289b4e1e, 0x0198d9b3,
    ],
    [
        0x070a92e6, 0x2f1b6cb3, 0x535008bb, 0x35af339a, 0x7a38e92c, 0x4ff71b5c, 0x3b193aba, 0x34d12a1e, 0x17e94240,
        0x2ec214dc, 0x43e09385, 0x7d546918, 0x71af9dfd, 0x761a21bb, 0x43fdc986, 0x05dda714, 0x2d0e78b5, 0x1fcd387b,
        0x76e10a76, 0x28a112d5, 0x1a7bd787, 0x40190de2, 0x2e27906a, 0x2033954e,
    ],
    [
        0x20afd2c8, 0x71b5ecb2, 0x57828fb3, 0x222851d8, 0x732df0e9, 0x73f48435, 0x7e63ea98, 0x058be348, 0x229e7a5f,
        0x04576a2f, 0x29939f10, 0x7afd830a, 0x5d6dd961, 0x0eb65d94, 0x39da2b79, 0x36bce8ba, 0x5f53a7d4, 0x383b1cd2,
        0x1fdc3c5f, 0x7d9ca544, 0x77480711, 0x36c51a1a, 0x009ea59b, 0x731b17fd,
    ],
    [
        0x201359bd, 0x22bf6499, 0x610f1a29, 0x3c73aa45, 0x6a092599, 0x1c7cb703, 0x79533459, 0x7ef62d86, 0x5ab925ab,
        0x67722ab1, 0x33ca4cff, 0x007f7dce, 0x0eeac41e, 0x4724bea7, 0x45eaf64f, 0x21a6c90f, 0x094b4150, 0x0d942630,
        0x18712c30, 0x3a470338, 0x6eba7720, 0x487827c8, 0x77013a6d, 0x4ad07390,
    ],
    [
        0x57d802ea, 0x720f5fd4, 0x5b8a5357, 0x3649db1f, 0x35ea476a, 0x4c6589f5, 0x02c9f31f, 0x16d04670, 0x62d74b20,
        0x1de813cc, 0x189966ed, 0x527add06, 0x1704f5af, 0x000f1703, 0x00152a1f, 0x2f49a365, 0x40ee4288, 0x0ab86260,
        0x080c8576, 0x36c6cc05, 0x0ab9346f, 0x62aa3ec8, 0x51109797, 0x0feb1585,
    ],
    [
        0x04700024, 0x01dee723, 0x5cd4aaa8, 0x1fe43ce5, 0x25c31267, 0x58512b48, 0x54147539, 0x4e340ab9, 0x563fbaeb,
        0x60c8353a, 0x65a12d49, 0x6c499fb2, 0x7ea07556, 0x396e2bbb, 0x31a318f1, 0x11f855ae, 0x6edffb87, 0x59977042,
        0x6ec5fa94, 0x75b4f690, 0x44b6fc61, 0x02a8bed8, 0x4c88c824, 0x08e31432,
    ],
    [
        0x09a4c09f, 0x4796b47d, 0x215b7e75, 0x0c639599, 0x0d93dd4c, 0x2fac41de, 0x4f46dadd, 0x03905848, 0x2b1c39c1,
        0x25fff199, 0x38621f7b, 0x69e59315, 0x1874c308, 0x024a3959, 0x2bae1f12, 0x3c200626, 0x6ba5d369, 0x2fe9b97e,
        0x674cc08e, 0x2cbb9657, 0x550e56c2, 0x5b80e0ec, 0x6549ccff, 0x54e3e61a,
    ],
    [
        0x0fa689e3, 0x2c534848, 0x1eb24382, 0x61b959b5, 0x4d5f001e, 0x003a95cd, 0x1edd4507, 0x621e895d, 0x7dc6e599,
        0x0fbc2771, 0x152d0879, 0x77801087, 0x6a2dd731, 0x3644aba2, 0x2e43a814, 0x12ff923f, 0x01cfe2c9, 0x35f8a572,
        0x5789fd35, 0x16f39e7a, 0x7c0ca31c, 0x01016283, 0x2c9dcd96, 0x5d3c6f4e,
    ],
    [
        0x0058a186, 0x16354360, 0x502a262b, 0x2b56f93e, 0x0bc41ecb, 0x33c83e8b, 0x21968fc3, 0x6364490c, 0x16a45aa5,
        0x286d873f, 0x2be17254, 0x381fbc06, 0x0df309aa, 0x15d48b84, 0x0fb2c5dd, 0x7c440d21, 0x74908f00, 0x75520624,
        0x7e58f065, 0x141e1e41, 0x6582f4ae, 0x2c4479e5, 0x7a09fff8, 0x1baa979f,
    ],
    [
        0x45ab39bd, 0x774f78bc, 0x3c5f9aa2, 0x115d9dc9, 0x4b1546d7, 0x196c1a55, 0x6a88fb5e, 0x4c1ca910, 0x34869067,
        0x2662dcbb, 0x0a4625d4, 0x25b121c8, 0x1a50ccd2, 0x490ea316, 0x42556ffa, 0x6b5e4f88, 0x329faf33, 0x54f39a88,
        0x3b411e09, 0x6950ae8e, 0x310a912c, 0x63bddcba, 0x347977c0, 0x52831335,
    ],
    [
        0x41f32fc6, 0x67dd5acb, 0x41ae544e, 0x1d83750a, 0x4bb58d20, 0x2f5496ee, 0x353819ec, 0x412ee425, 0x1bfd2747,
        0x32a14699, 0x2f7be906, 0x38afda41, 0x5b1e6316, 0x7b810b48, 0x6aebb30d, 0x55d94f89, 0x69db4833, 0x3a6ecb6c,
        0x50e7d206, 0x148a4b69, 0x1ac5548d, 0x40019cf9, 0x1e566f2a, 0x0998a950,
    ],
    [
        0x5bc887f0, 0x73fbbd18, 0x341e05a8, 0x7d0597d5, 0x582308d9, 0x7a98addf, 0x0938b854, 0x544bf13d, 0x50090144,
        0x13baf374, 0x1896a8d5, 0x75ea7475, 0x23510dd8, 0x72c93bcc, 0x1c41410e, 0x4b72d5f9, 0x103ccc4e, 0x3896bef2,
        0x2c5e0b1c, 0x1e2096de, 0x15594d47, 0x04e035ce, 0x2785d1b1, 0x795bc87d,
    ],
    [
        0x373fecbf, 0x0b18c3a0, 0x6516874a, 0x2b567be9, 0x5a2a3d1b, 0x74d99c04, 0x437de605, 0x047df991, 0x322faad4,
        0x2ef2f76f, 0x5f9e7278, 0x62740235, 0x18c1e8c2, 0x0691e203, 0x3324646d, 0x59542c9f, 0x32433d0d, 0x42c17492,
        0x45ac808a, 0x685394e0, 0x316f7193, 0x5ea108a0, 0x6bb3f12f, 0x232f8865,
    ],
    [
        0x7c162b62, 0x52aa9e45, 0x1b69f8db, 0x3ec35206, 0x1ef086dd, 0x34d7a5e3, 0x33aeea57, 0x03565cc8, 0x5bc5fd47,
        0x47adc343, 0x1d5857a2, 0x5e7ece76, 0x0239fba3, 0x58bdead4, 0x41671aef, 0x3c8a9189, 0x7342ed52, 0x19871456,
        0x573a02c8, 0x2ec8ad55, 0x09c4a997, 0x34b9b63a, 0x226da984, 0x6b31d16e,
    ],
    [
        0x458384d2, 0x353911e1, 0x4cfd1256, 0x163c23af, 0x7609c5e0, 0x76596c08, 0x087adac7, 0x4fd4b62c, 0x3692a037,
        0x51c54b62, 0x133daf4d, 0x0c76f623, 0x387d21f3, 0x6034abe5, 0x7c982e2b, 0x63a266b4, 0x4f2b17b8, 0x0bd62f1d,
        0x70e37a7c, 0x4f162da9, 0x38f0e527, 0x6ce798d7, 0x6c74250b, 0x606f2fad,
    ],
    [
        0x212b041d, 0x6724fd32, 0x73aaf9af, 0x3ae9b76b, 0x014fe151, 0x37687943, 0x36bb7786, 0x01da85ef, 0x28c618ae,
        0x36706580, 0x3f5f610d, 0x2e0b9391, 0x5750e38d, 0x00b48d71, 0x0f1f1d7a, 0x7107c415, 0x35c1e287, 0x26ccce2f,
        0x4e29277a, 0x1580ee9d, 0x18136f74, 0x530f32ad, 0x5a19b05d, 0x3d38b320,
    ],
    [
        0x6a3bf1e4, 0x39e9edbb, 0x2ce6a59e, 0x2df215e1, 0x216a17ba, 0x3a8f3cfa, 0x0a14d990, 0x1162e529, 0x1213c181,
        0x3daa68f5, 0x16c570ff, 0x1063321c, 0x06a2d0e8, 0x17c094a4, 0x39a5d9c9, 0x086d4802, 0x67ab7fe3, 0x67f51392,
        0x3649c2ac, 0x62aa8cf8, 0x55b6fdbb, 0x55c3e972, 0x2f865724, 0x314fa653,
    ],
    [
        0x029f66f1, 0x016f80a2, 0x4b70e0c2, 0x1782f9ab, 0x697578ee, 0x07b2c8b7, 0x123f6681, 0x2b78db24, 0x2cd8db9d,
        0x302947b1, 0x04f4c99a, 0x1f8bcbbd, 0x61c782ea, 0x3459928c, 0x3efec720, 0x24f2b8f6, 0x5dec66b5, 0x622386cc,
        0x26b70002, 0x1fa0d640, 0x6edeaa0a, 0x670ff3e1, 0x18641d8e, 0x43b68197,
    ],
    [
        0x315b1707, 0x46db526a, 0x02fa5277, 0x36f6edf9, 0x31ad912b, 0x7d518ebd, 0x61db2eea, 0x0ba28bad, 0x3c839e59,
        0x7ed007f1, 0x74447f8a, 0x6b4ce5b7, 0x7272e3a4, 0x192257d1, 0x5f882281, 0x5f890768, 0x47eec4cb, 0x2ef3e6c8,
        0x43d6e4e2, 0x668ce6ba, 0x50679e00, 0x24c067a8, 0x605be47c, 0x324ac2ec,
    ],
    // Terminal full rounds (4)
    [
        0x5883788f, 0x7eba66af, 0x23620f78, 0x44492c9a, 0x7cc098a4, 0x705191fa, 0x2f7185e2, 0x6ebbb07e, 0x23508c3b,
        0x6cb0f0f4, 0x1190a8c0, 0x60f8f1d0, 0x316c16a1, 0x440742c7, 0x7643f142, 0x642f9668, 0x214b7566, 0x52a5c469,
        0x1bfd90da, 0x1d7d8076, 0x6e06d1e8, 0x7d672e6d, 0x6fd2e3e3, 0x3257ae18,
    ],
    [
        0x75861a51, 0x0e2996fe, 0x2bdc228b, 0x6879fcb8, 0x14ca9b1c, 0x29953d92, 0x36ee671d, 0x31366e47, 0x79c4f5f2,
        0x2b8c8639, 0x073a293d, 0x32802c31, 0x4894d32f, 0x06acc989, 0x40d852b1, 0x508857c4, 0x2ffe504d, 0x18be00c1,
        0x75a114e9, 0x4ed5922a, 0x1060ee72, 0x2176563c, 0x0b91b242, 0x6bfbf1a4,
    ],
    [
        0x06f94470, 0x694f4383, 0x53cada3e, 0x1527bfd8, 0x2bdfe868, 0x120c2d2c, 0x7dfd6309, 0x10b619c2, 0x0550bc7f,
        0x488cf3dc, 0x4c5454a2, 0x00be2976, 0x349c9669, 0x2b4eb07d, 0x0450bf40, 0x58de7343, 0x3495a265, 0x2305e3b7,
        0x661dd781, 0x1c183983, 0x46992791, 0x3eb3751f, 0x38f728c8, 0x775d0a30,
    ],
    [
        0x7636645a, 0x7125aa5d, 0x0c3f2dca, 0x13b595cc, 0x5a5e9bce, 0x54bb3456, 0x069a1a5a, 0x7b9f15ee, 0x50150189,
        0x68c9157b, 0x07e06e22, 0x568aecdb, 0x1403f847, 0x436cf5da, 0x3f09c026, 0x652f7b1b, 0x3e8607f3, 0x5bb37c57,
        0x1b1a9ecf, 0x39d11cb0, 0x1841a51c, 0x1251ad48, 0x74fb5edd, 0x21fa33c6,
    ],
]);

// =========================================================================
// Accessors
// =========================================================================

pub fn poseidon1_24_round_constants() -> &'static [[KoalaBear; 24]; POSEIDON1_N_ROUNDS_24] {
    &POSEIDON1_RC_24
}

#[inline(always)]
pub fn poseidon1_24_initial_constants() -> &'static [[KoalaBear; 24]] {
    &POSEIDON1_RC_24[..POSEIDON1_HALF_FULL_ROUNDS_24]
}

#[inline(always)]
pub fn poseidon1_24_partial_constants() -> &'static [[KoalaBear; 24]] {
    &POSEIDON1_RC_24[POSEIDON1_HALF_FULL_ROUNDS_24..POSEIDON1_HALF_FULL_ROUNDS_24 + POSEIDON1_PARTIAL_ROUNDS_24]
}

#[inline(always)]
pub fn poseidon1_24_final_constants() -> &'static [[KoalaBear; 24]] {
    &POSEIDON1_RC_24[POSEIDON1_HALF_FULL_ROUNDS_24 + POSEIDON1_PARTIAL_ROUNDS_24..]
}

pub fn poseidon1_24_sparse_m_i() -> &'static [[KoalaBear; 24]; 24] {
    &precomputed_24().sparse_m_i
}

pub fn poseidon1_24_sparse_first_row() -> &'static Vec<[KoalaBear; 24]> {
    &precomputed_24().sparse_first_row
}

pub fn poseidon1_24_sparse_v() -> &'static Vec<[KoalaBear; 24]> {
    &precomputed_24().sparse_v
}

pub fn poseidon1_24_sparse_first_round_constants() -> &'static [KoalaBear; 24] {
    &precomputed_24().sparse_first_round_constants
}

pub fn poseidon1_24_sparse_scalar_round_constants() -> &'static Vec<KoalaBear> {
    &precomputed_24().sparse_round_constants
}

#[derive(Clone, Debug)]
pub struct Poseidon1KoalaBear24 {
    pre: &'static Precomputed24,
}

impl Poseidon1KoalaBear24 {
    #[inline(always)]
    #[allow(clippy::needless_range_loop)]
    fn permute_generic<R: Algebra<KoalaBear> + InjectiveMonomial<3>>(&self, state: &mut [R; 24]) {
        // Initial full rounds: AddRC + S-box + Karatsuba MDS.
        for rc in poseidon1_24_initial_constants() {
            Self::full_round(state, rc);
        }

        // Partial rounds via sparse decomposition.
        // Add first-round constants.
        for (s, &c) in state.iter_mut().zip(self.pre.sparse_first_round_constants.iter()) {
            *s += c;
        }
        // Apply dense transition matrix m_i (once).
        {
            let input = *state;
            for i in 0..24 {
                state[i] = R::ZERO;
                for j in 0..24 {
                    state[i] += input[j] * self.pre.sparse_m_i[i][j];
                }
            }
        }
        // Loop over partial rounds: S-box + scalar constant + cheap_matmul.
        let rounds_p = self.pre.sparse_first_row.len();
        for r in 0..rounds_p {
            state[0] = state[0].injective_exp_n();
            if r < rounds_p - 1 {
                state[0] += self.pre.sparse_round_constants[r];
            }
            // cheap_matmul: O(24) sparse matrix multiply.
            let old_s0 = state[0];
            state[0] = parity_dot(*state, self.pre.sparse_first_row[r]);
            for i in 1..24 {
                state[i] += old_s0 * self.pre.sparse_v[r][i - 1];
            }
        }

        // Terminal full rounds.
        for rc in poseidon1_24_final_constants() {
            Self::full_round(state, rc);
        }
    }

    #[inline(always)]
    fn full_round<R: Algebra<KoalaBear> + InjectiveMonomial<3>>(state: &mut [R; 24], rc: &[KoalaBear; 24]) {
        for (s, &c) in state.iter_mut().zip(rc.iter()) {
            *s += c;
        }
        for s in state.iter_mut() {
            *s = s.injective_exp_n();
        }
        mds_karatsuba_24(state);
    }

    /// NEON-specific fast path with pre-packed constants and latency hiding.
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    #[inline(always)]
    fn permute_neon(&self, state: &mut [PackedKB; 24]) {
        use crate::PackedMontyField31Neon;
        use crate::exp_small;
        use crate::{InternalLayer24, add_rc_and_sbox};
        use core::mem::transmute;

        let neon = &self.pre.neon;

        // --- Initial full rounds (first 3 of 4) ---
        for round_constants in &neon.packed_initial_rc {
            for (s, &rc) in state.iter_mut().zip(round_constants.iter()) {
                add_rc_and_sbox::<FP, 3>(s, rc);
            }
            neon_karatsuba::mds_karatsuba_24_neon(state, &neon.mds_col);
        }

        // --- Last initial full round: AddRC + S-box, then fused (m_i * MDS) ---
        {
            for (s, &rc) in state.iter_mut().zip(neon.packed_last_initial_rc.iter()) {
                add_rc_and_sbox::<FP, 3>(s, rc);
            }
            let input = *state;
            for (i, s) in state.iter_mut().enumerate() {
                *s = PackedMontyField31Neon::<FP>::dot_product(&input, &neon.packed_fused_mi_mds[i])
                    + neon.packed_fused_bias[i];
            }
        }

        // --- Partial rounds with latency hiding via InternalLayer24 split ---
        {
            let mut split = InternalLayer24::from_packed_field_array(*state);

            for r in 0..POSEIDON1_PARTIAL_ROUNDS_24 {
                // PATH A (high latency): S-box on s0.
                unsafe {
                    let s0_signed = split.s0.to_signed_vector();
                    let s0_sboxed = exp_small::<FP, 3>(s0_signed);
                    split.s0 = PackedMontyField31Neon::from_vector(s0_sboxed);
                }

                // Add scalar round constant (except last round).
                if r < POSEIDON1_PARTIAL_ROUNDS_24 - 1 {
                    split.s0 += neon.packed_round_constants[r];
                }

                // PATH B (can overlap with S-box): partial dot product on s_hi.
                let s_hi: &[PackedKB; 23] = unsafe { transmute(&split.s_hi) };
                let first_row = &neon.packed_sparse_first_row[r];
                let first_row_hi: &[PackedKB; 23] = first_row[1..].try_into().unwrap();
                let partial_dot = PackedMontyField31Neon::<FP>::dot_product(s_hi, first_row_hi);

                // SERIAL: complete s0 = first_row[0] * s0 + partial_dot.
                let s0_val = split.s0;
                split.s0 = s0_val * first_row[0] + partial_dot;

                // Rank-1 update: s_hi[j] += s0_old * v[j].
                let v = &neon.packed_sparse_v[r];
                let s_hi_mut: &mut [PackedKB; 23] = unsafe { transmute(&mut split.s_hi) };
                for j in 0..23 {
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
            neon_karatsuba::mds_karatsuba_24_neon(state, &neon.mds_col);
        }
    }

    /// Compression mode: output = permute(input) + input.
    #[inline(always)]
    pub fn compress_in_place<R: Algebra<KoalaBear> + InjectiveMonomial<3> + Send + Sync + 'static>(
        &self,
        state: &mut [R; 24],
    ) {
        let initial = *state;
        Permutation::permute_mut(self, state);
        for (s, init) in state.iter_mut().zip(initial) {
            *s += init;
        }
    }
}

impl<R: Algebra<KoalaBear> + InjectiveMonomial<3> + Send + Sync + 'static> Permutation<[R; 24]>
    for Poseidon1KoalaBear24
{
    fn permute_mut(&self, input: &mut [R; 24]) {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        {
            if std::any::TypeId::of::<R>() == std::any::TypeId::of::<PackedKB>() {
                let neon_state: &mut [PackedKB; 24] = unsafe { &mut *(input as *mut [R; 24] as *mut [PackedKB; 24]) };
                self.permute_neon(neon_state);
                return;
            }
        }
        self.permute_generic(input);
    }
}

pub fn default_koalabear_poseidon1_24() -> Poseidon1KoalaBear24 {
    Poseidon1KoalaBear24 { pre: precomputed_24() }
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

        use crate::{KoalaBear, default_koalabear_poseidon1_24};

        #[test]
        fn plonky3_test() {
            let poseidon1 = default_koalabear_poseidon1_24();
            let mut input: [KoalaBear; 24] = KoalaBear::new_array([
                0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
            ]);
            poseidon1.permute_mut(&mut input);
            dbg!(&input);
        }

         */
        let p1 = default_koalabear_poseidon1_24();
        let mut input: [KoalaBear; 24] = KoalaBear::new_array([
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
        ]);
        p1.permute_mut(&mut input);
        let vals: Vec<u32> = input.iter().map(|x| x.as_canonical_u32()).collect();
        assert_eq!(
            vals,
            vec![
                511672087, 215882318, 237782537, 740528428, 712760904, 54615367, 751514671, 110231969, 1905276435,
                992525666, 918312360, 18628693, 749929200, 1916418953, 691276896, 1112901727, 1163558623, 882867603,
                673396520, 1480278156, 1402044758, 1693467175, 1766273044, 433841551,
            ]
        );
    }
}
