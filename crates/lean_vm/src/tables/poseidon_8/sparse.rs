//! Sparse matrix decomposition for Poseidon1-8 partial rounds.
//!
//! Port of `plonky3/poseidon1/src/utils.rs` specialised to the Goldilocks width-8
//! configuration. Produces the transition matrix `m_i`, the per-round sparse
//! matrices (`sparse_first_row[r]`, `v[r]`), and the compressed round constants
//! (`first_round_constants` + per-round scalar `round_constants`), so that all
//! 22 partial rounds can be constrained with 2 committed columns each instead
//! of the naive 9.
//!
//! References:
//! - Grassi et al., "Poseidon: A New Hash Function for Zero-Knowledge Proof
//!   Systems", USENIX Security 2021, Appendix B.
//! - `plonky3/poseidon1/src/{utils.rs, internal.rs}`.

use std::sync::OnceLock;

use backend::{
    Field, GOLDILOCKS_POSEIDON1_RC_8, MDS8_ROW, POSEIDON1_HALF_FULL_ROUNDS, POSEIDON1_PARTIAL_ROUNDS,
    PrimeCharacteristicRing,
};

use crate::F;

pub(super) const WIDTH: usize = 8;
pub(super) const PARTIAL_ROUNDS: usize = POSEIDON1_PARTIAL_ROUNDS;

/// Precomputed constants for the sparse partial-round layer.
#[derive(Debug, Clone)]
pub(super) struct PartialConstants {
    /// Absorbs the original partial-round 0 vector plus backward-substituted
    /// remainders from rounds 1..RP. Added once before the m_i multiply.
    pub first_round_constants: [F; WIDTH],
    /// Dense transition matrix applied once after adding
    /// `first_round_constants` and before the sparse-round loop.
    pub m_i: [[F; WIDTH]; WIDTH],
    /// Per-round pre-assembled first row of the sparse matrix:
    /// `[mds[0][0], w_hat[0], …, w_hat[WIDTH-2]]`.
    pub sparse_first_row: [[F; WIDTH]; PARTIAL_ROUNDS],
    /// Per-round first-column coefficients (WIDTH-1 entries; we use `[F; WIDTH-1]`).
    pub v: [[F; WIDTH - 1]; PARTIAL_ROUNDS],
    /// Scalar round constants for partial rounds 0..RP-1 (the last round uses
    /// no additive constant — it was absorbed by the backward substitution).
    pub round_constants: [F; PARTIAL_ROUNDS - 1],
}

static PARTIAL_CONSTANTS: OnceLock<PartialConstants> = OnceLock::new();

pub(super) fn get_partial_constants() -> &'static PartialConstants {
    PARTIAL_CONSTANTS.get_or_init(compute_partial_constants)
}

/// Build the dense WxW circulant MDS matrix from `MDS8_ROW`.
///
/// `M[i][j] = MDS8_ROW[(j - i) mod W]`, stored as `F`.
pub(super) fn mds_dense() -> [[F; WIDTH]; WIDTH] {
    let mut m = [[F::ZERO; WIDTH]; WIDTH];
    for i in 0..WIDTH {
        for j in 0..WIDTH {
            m[i][j] = F::from_u64(MDS8_ROW[(j + WIDTH - i) % WIDTH] as u64);
        }
    }
    m
}

fn matrix_transpose(m: &[[F; WIDTH]; WIDTH]) -> [[F; WIDTH]; WIDTH] {
    let mut r = [[F::ZERO; WIDTH]; WIDTH];
    for i in 0..WIDTH {
        for j in 0..WIDTH {
            r[i][j] = m[j][i];
        }
    }
    r
}

fn matrix_mul(a: &[[F; WIDTH]; WIDTH], b: &[[F; WIDTH]; WIDTH]) -> [[F; WIDTH]; WIDTH] {
    let mut c = [[F::ZERO; WIDTH]; WIDTH];
    for i in 0..WIDTH {
        for j in 0..WIDTH {
            let mut acc = F::ZERO;
            for k in 0..WIDTH {
                acc += a[i][k] * b[k][j];
            }
            c[i][j] = acc;
        }
    }
    c
}

fn matrix_vec_mul(m: &[[F; WIDTH]; WIDTH], v: &[F; WIDTH]) -> [F; WIDTH] {
    let mut r = [F::ZERO; WIDTH];
    for i in 0..WIDTH {
        let mut acc = F::ZERO;
        for j in 0..WIDTH {
            acc += m[i][j] * v[j];
        }
        r[i] = acc;
    }
    r
}

fn matrix_inverse(m: &[[F; WIDTH]; WIDTH]) -> [[F; WIDTH]; WIDTH] {
    let mut aug = *m;
    let mut inv = [[F::ZERO; WIDTH]; WIDTH];
    for (i, row) in inv.iter_mut().enumerate().take(WIDTH) {
        row[i] = F::ONE;
    }
    for col in 0..WIDTH {
        let pivot = (col..WIDTH)
            .find(|&r| aug[r][col] != F::ZERO)
            .expect("mds matrix is singular");
        if pivot != col {
            aug.swap(col, pivot);
            inv.swap(col, pivot);
        }
        let pivot_inv = aug[col][col].inverse();
        for j in 0..WIDTH {
            aug[col][j] *= pivot_inv;
            inv[col][j] *= pivot_inv;
        }
        for i in 0..WIDTH {
            if i == col {
                continue;
            }
            let factor = aug[i][col];
            if factor == F::ZERO {
                continue;
            }
            let aug_row = aug[col];
            let inv_row = inv[col];
            for j in 0..WIDTH {
                aug[i][j] -= factor * aug_row[j];
                inv[i][j] -= factor * inv_row[j];
            }
        }
    }
    inv
}

/// Inverse of the bottom-right (W-1)x(W-1) submatrix `m[1..][1..]`.
fn submatrix_inverse(m: &[[F; WIDTH]; WIDTH]) -> [[F; WIDTH - 1]; WIDTH - 1] {
    const N: usize = WIDTH - 1;
    let mut sub = [[F::ZERO; N]; N];
    for i in 0..N {
        for j in 0..N {
            sub[i][j] = m[i + 1][j + 1];
        }
    }
    let mut inv = [[F::ZERO; N]; N];
    for (i, row) in inv.iter_mut().enumerate().take(N) {
        row[i] = F::ONE;
    }
    for col in 0..N {
        let pivot = (col..N)
            .find(|&r| sub[r][col] != F::ZERO)
            .expect("mds submatrix is singular");
        if pivot != col {
            sub.swap(col, pivot);
            inv.swap(col, pivot);
        }
        let pivot_inv = sub[col][col].inverse();
        for j in 0..N {
            sub[col][j] *= pivot_inv;
            inv[col][j] *= pivot_inv;
        }
        for i in 0..N {
            if i == col {
                continue;
            }
            let factor = sub[i][col];
            if factor == F::ZERO {
                continue;
            }
            let sub_row = sub[col];
            let inv_row = inv[col];
            for j in 0..N {
                sub[i][j] -= factor * sub_row[j];
                inv[i][j] -= factor * inv_row[j];
            }
        }
    }
    inv
}

type EquivalentMatrices = ([[F; WIDTH]; WIDTH], Vec<[F; WIDTH]>, Vec<[F; WIDTH]>);

/// Factor the dense MDS matrix into `RP` sparse factors.
///
/// Returns `(m_i, v_collection, w_hat_collection)` all in forward application
/// order; `v_collection[r]` and `w_hat_collection[r]` have `WIDTH-1` meaningful
/// entries (the last slot is zero padding for fixed-size arrays).
fn compute_equivalent_matrices(mds: &[[F; WIDTH]; WIDTH], rounds_p: usize) -> EquivalentMatrices {
    let mut v_collection: Vec<[F; WIDTH]> = Vec::with_capacity(rounds_p);
    let mut w_hat_collection: Vec<[F; WIDTH]> = Vec::with_capacity(rounds_p);

    let mds_t = matrix_transpose(mds);
    let mut m_mul = mds_t;
    let mut m_i = [[F::ZERO; WIDTH]; WIDTH];

    for _ in 0..rounds_p {
        // v = first row of m_mul (excl [0,0]). In the transposed domain this is
        // the first column of M'' in the non-transposed view.
        let v_arr: [F; WIDTH] = std::array::from_fn(|j| if j < WIDTH - 1 { m_mul[0][j + 1] } else { F::ZERO });

        // w = first column of m_mul (excl [0,0]).
        let mut w = [F::ZERO; WIDTH - 1];
        for i in 0..WIDTH - 1 {
            w[i] = m_mul[i + 1][0];
        }
        // w_hat = M_hat^{-1} * w.
        let m_hat_inv = submatrix_inverse(&m_mul);
        let w_hat_arr: [F; WIDTH] = std::array::from_fn(|i| {
            if i < WIDTH - 1 {
                let mut acc = F::ZERO;
                for k in 0..WIDTH - 1 {
                    acc += m_hat_inv[i][k] * w[k];
                }
                acc
            } else {
                F::ZERO
            }
        });

        v_collection.push(v_arr);
        w_hat_collection.push(w_hat_arr);

        // m_i = identity-like with m_mul's first row/column stored, then
        // "absorb" the rest: first column zeroed, first row zeroed, [0][0]=1.
        m_i = m_mul;
        m_i[0][0] = F::ONE;
        for row in m_i.iter_mut().take(WIDTH).skip(1) {
            row[0] = F::ZERO;
        }
        for entry in m_i[0].iter_mut().take(WIDTH).skip(1) {
            *entry = F::ZERO;
        }

        // Accumulate: m_mul = M^T * m_i.
        m_mul = matrix_mul(&mds_t, &m_i);
    }

    // Transpose m_i back (HorizenLabs works in the transposed domain).
    let m_i_returned = matrix_transpose(&m_i);

    v_collection.reverse();
    w_hat_collection.reverse();

    (m_i_returned, v_collection, w_hat_collection)
}

/// Backward-substitute partial round constants through M^{-1}, producing the
/// full first-round vector and per-round scalar offsets.
fn equivalent_round_constants(partial_rc: &[[F; WIDTH]], mds_inv: &[[F; WIDTH]; WIDTH]) -> ([F; WIDTH], Vec<F>) {
    let rounds_p = partial_rc.len();
    let mut opt_partial_rc = vec![F::ZERO; rounds_p];

    let mut tmp = partial_rc[rounds_p - 1];
    for i in (0..rounds_p - 1).rev() {
        let inv_cip = matrix_vec_mul(mds_inv, &tmp);
        opt_partial_rc[i + 1] = inv_cip[0];
        tmp = partial_rc[i];
        for j in 1..WIDTH {
            tmp[j] += inv_cip[j];
        }
    }
    let first_round_constants = tmp;
    let opt_partial_rc = opt_partial_rc[1..].to_vec();
    (first_round_constants, opt_partial_rc)
}

fn compute_partial_constants() -> PartialConstants {
    let mds = mds_dense();
    let mds_inv = matrix_inverse(&mds);

    // Slice out the partial-round RCs from the monolithic RC table.
    let partial_rc: Vec<[F; WIDTH]> = (0..PARTIAL_ROUNDS)
        .map(|r| GOLDILOCKS_POSEIDON1_RC_8[POSEIDON1_HALF_FULL_ROUNDS + r])
        .collect();

    let (first_round_constants, round_constants_vec) = equivalent_round_constants(&partial_rc, &mds_inv);
    let (m_i, v_collection, w_hat_collection) = compute_equivalent_matrices(&mds, PARTIAL_ROUNDS);

    // sparse_first_row[r] = [mds[0][0], w_hat[r][0], …, w_hat[r][W-2]].
    let mds_0_0 = mds[0][0];
    let mut sparse_first_row = [[F::ZERO; WIDTH]; PARTIAL_ROUNDS];
    for r in 0..PARTIAL_ROUNDS {
        sparse_first_row[r][0] = mds_0_0;
        for i in 1..WIDTH {
            sparse_first_row[r][i] = w_hat_collection[r][i - 1];
        }
    }

    // v[r] stripped to [F; WIDTH-1] (drop the zero tail).
    let mut v = [[F::ZERO; WIDTH - 1]; PARTIAL_ROUNDS];
    for r in 0..PARTIAL_ROUNDS {
        for i in 0..WIDTH - 1 {
            v[r][i] = v_collection[r][i];
        }
    }

    let mut round_constants = [F::ZERO; PARTIAL_ROUNDS - 1];
    round_constants[..(PARTIAL_ROUNDS - 1)].copy_from_slice(&round_constants_vec[..(PARTIAL_ROUNDS - 1)]);

    PartialConstants {
        first_round_constants,
        m_i,
        sparse_first_row,
        v,
        round_constants,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::{POSEIDON1_HALF_FULL_ROUNDS, PrimeField64};
    use utils::poseidon8_compress;

    fn sbox7(x: F) -> F {
        let x2 = x * x;
        let x4 = x2 * x2;
        x4 * x2 * x
    }

    /// Textbook (non-sparse) partial-round phase, used as a reference.
    fn textbook_partial_phase(mut state: [F; WIDTH]) -> [F; WIDTH] {
        let mds = mds_dense();
        for r in 0..PARTIAL_ROUNDS {
            let abs = POSEIDON1_HALF_FULL_ROUNDS + r;
            for i in 0..WIDTH {
                state[i] = state[i] + GOLDILOCKS_POSEIDON1_RC_8[abs][i];
            }
            state[0] = sbox7(state[0]);
            state = matrix_vec_mul(&mds, &state);
        }
        state
    }

    /// Sparse partial-round phase — what the AIR witness computes.
    fn sparse_partial_phase(mut state: [F; WIDTH]) -> [F; WIDTH] {
        let c = get_partial_constants();
        for i in 0..WIDTH {
            state[i] = state[i] + c.first_round_constants[i];
        }
        state = matrix_vec_mul(&c.m_i, &state);
        for r in 0..PARTIAL_ROUNDS - 1 {
            state[0] = sbox7(state[0]);
            state[0] = state[0] + c.round_constants[r];
            let old_s0 = state[0];
            // new_state[0] = dot(sparse_first_row[r], state).
            let mut acc = F::ZERO;
            for j in 0..WIDTH {
                acc = acc + c.sparse_first_row[r][j] * state[j];
            }
            state[0] = acc;
            for i in 1..WIDTH {
                state[i] = state[i] + c.v[r][i - 1] * old_s0;
            }
        }
        // last round — no RC.
        {
            let r = PARTIAL_ROUNDS - 1;
            state[0] = sbox7(state[0]);
            let old_s0 = state[0];
            let mut acc = F::ZERO;
            for j in 0..WIDTH {
                acc = acc + c.sparse_first_row[r][j] * state[j];
            }
            state[0] = acc;
            for i in 1..WIDTH {
                state[i] = state[i] + c.v[r][i - 1] * old_s0;
            }
        }
        state
    }

    /// The sparse decomposition must reproduce the textbook phase bit-for-bit.
    #[test]
    fn sparse_matches_textbook() {
        let mut seed = 0u64;
        for trial in 0..4 {
            seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let input: [F; WIDTH] =
                std::array::from_fn(|i| F::from_u64(seed.wrapping_mul(i as u64 + 1 + trial as u64)));
            let a = textbook_partial_phase(input);
            let b = sparse_partial_phase(input);
            for i in 0..WIDTH {
                assert_eq!(
                    a[i].as_canonical_u64(),
                    b[i].as_canonical_u64(),
                    "trial {trial} lane {i}"
                );
            }
        }
    }

    /// End-to-end: a full permutation via the sparse decomposition must match
    /// `poseidon8_compress` (Davies-Meyer around the Goldilocks Poseidon1-8).
    #[test]
    fn full_permutation_matches_poseidon8_compress() {
        let input: [F; WIDTH] = std::array::from_fn(|i| F::from_u64(i as u64 * 37 + 1));
        // Initial full rounds.
        let mut state = input;
        let mds = mds_dense();
        for round in 0..POSEIDON1_HALF_FULL_ROUNDS {
            for i in 0..WIDTH {
                state[i] = state[i] + GOLDILOCKS_POSEIDON1_RC_8[round][i];
            }
            for i in 0..WIDTH {
                state[i] = sbox7(state[i]);
            }
            state = matrix_vec_mul(&mds, &state);
        }
        state = sparse_partial_phase(state);
        for round in 0..POSEIDON1_HALF_FULL_ROUNDS {
            let abs = POSEIDON1_HALF_FULL_ROUNDS + PARTIAL_ROUNDS + round;
            for i in 0..WIDTH {
                state[i] = state[i] + GOLDILOCKS_POSEIDON1_RC_8[abs][i];
            }
            for i in 0..WIDTH {
                state[i] = sbox7(state[i]);
            }
            state = matrix_vec_mul(&mds, &state);
        }
        // Davies-Meyer.
        let output: [F; 4] = std::array::from_fn(|i| state[i] + input[i]);
        let expected = poseidon8_compress(input);
        assert_eq!(output, expected);
    }
}
