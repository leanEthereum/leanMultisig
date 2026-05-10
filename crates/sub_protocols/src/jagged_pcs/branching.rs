//! Width-6 read-once branching program for the indicator function
//! `g_u(z_row, z_col, i, t_prev, t_next)` from fancy jagged.
//!
//! The function returns 1 iff:
//!   * `i = t_prev + z_row * 2^u + z_col` (as integers); AND
//!   * `i < t_next`.
//!
//! The BP processes the m bits of `(i, t_prev, t_next, z_row, z_col)` from
//! LSB to MSB. At each layer, the state is `(carry, lt)`:
//!   * `carry ∈ {0, 1, 2}` -- carry of the three-way addition. With carry-in
//!     up to 2 and three input bits each in {0, 1}, the per-layer sum is at
//!     most 5, so carry-out is at most 2 (a trit).
//!   * `lt ∈ {0, 1}` -- whether the bit-prefix of `i` seen so far is strictly
//!     less than the bit-prefix of `t_next` (LSB-first, so the most-recently
//!     read bit overrides earlier comparisons when it differs).
//!
//! State count = 3 * 2 = 6.
//!
//! Per layer the BP reads 5 bits in this order: (row, col, index, t_prev, t_next).
//! Wherever a coordinate doesn't actually appear at that layer (e.g. row at
//! layer p < u where row*2^u contributes 0, or col at layer p >= u where col
//! has fewer bits than the dense index), the corresponding eq factor is just
//! eq(0, sigma_bit), i.e. (1 - sigma_bit).
//!
//! Used as a sub-routine of the verifier in the jagged sumcheck.
use backend::*;

/// State variables of the branching program.
///
/// `carry` ∈ {0, 1, 2}, `lt` ∈ {0, 1}. State index = `carry + 3 * (lt as usize)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BpState {
    pub carry: u8,
    pub lt: bool,
}

pub const W: usize = 6;
pub const N_BITS_PER_LAYER: usize = 5;
pub const N_BIT_COMBOS: usize = 1 << N_BITS_PER_LAYER; // 32

impl BpState {
    pub const fn idx(self) -> usize {
        self.carry as usize + 3 * self.lt as usize
    }

    pub const INITIAL: Self = Self { carry: 0, lt: false };
    pub const SUCCESS: Self = Self { carry: 0, lt: true };
}

/// All 6 possible memory states.
pub fn all_states() -> [BpState; W] {
    let mut arr = [BpState::INITIAL; W];
    let mut i = 0;
    for lt in [false, true] {
        for carry in 0..3u8 {
            arr[i] = BpState { carry, lt };
            i += 1;
        }
    }
    arr
}

/// Bit vector at one layer: 5 booleans `(row, col, idx, prev, next)`.
#[derive(Clone, Copy, Debug)]
pub struct BitCombo {
    pub row: bool,
    pub col: bool,
    pub idx: bool,
    pub prev: bool,
    pub next: bool,
}

impl BitCombo {
    /// Decode index-in-cube into the named bits, matching the order
    /// expected by `eval_eq`. We use the convention that the 5-tuple passed
    /// to `eval_eq` is `[row, col, idx, prev, next]` (big-endian), so the
    /// hypercube index `i` reads MSB → LSB as `(row, col, idx, prev, next)`,
    /// i.e. `i = (row<<4) | (col<<3) | (idx<<2) | (prev<<1) | next`.
    pub const fn from_index(i: usize) -> Self {
        Self {
            row: (i >> 4) & 1 == 1,
            col: (i >> 3) & 1 == 1,
            idx: (i >> 2) & 1 == 1,
            prev: (i >> 1) & 1 == 1,
            next: i & 1 == 1,
        }
    }
}

/// Apply the BP transition. Returns `Some(next_state)` if the transition
/// succeeds (i.e. the addition is consistent with the index bit), else None.
pub fn transition(state: BpState, bits: BitCombo) -> Option<BpState> {
    let sum = bits.row as u8 + bits.col as u8 + bits.prev as u8 + state.carry;
    if (sum & 1) != bits.idx as u8 {
        return None;
    }
    let new_carry = sum >> 1;

    let new_lt = if bits.idx == bits.next {
        state.lt
    } else {
        // Bits differ at this (newly most-significant) position. Less-than
        // holds iff next bit is 1 and idx bit is 0.
        bits.next
    };

    Some(BpState {
        carry: new_carry,
        lt: new_lt,
    })
}

/// Branching program parameters held during evaluation. The "shifted row"
/// width `u` (i.e. `log_width` of the sub-table) determines the per-layer
/// re-indexing of `z_row` and `z_col`.
#[derive(Debug)]
pub struct BranchingProgram<'a, F: ExtensionField<PF<F>> + 'static> {
    pub z_row: &'a [F],
    pub z_col: &'a [F],
    pub z_index: &'a [F],
    pub log_width: usize,      // u
    pub log_dense_size: usize, // m (length of z_index, t_prev, t_next bit-vectors)
}

impl<'a, F: ExtensionField<PF<F>> + 'static> BranchingProgram<'a, F> {
    /// Returns the LSB-position-`p` bit of a big-endian point, treating bits
    /// past the end as zero.
    fn lsb_be(point: &[F], p: usize) -> F {
        if p >= point.len() {
            F::ZERO
        } else {
            point[point.len() - 1 - p]
        }
    }

    /// Returns the LSB-position-`p` bit of `z_row * 2^u`. This is the
    /// `(p - u)`-th LSB of `z_row` for `p >= u`, else zero.
    fn row_bit(&self, p: usize) -> F {
        if p < self.log_width {
            F::ZERO
        } else {
            Self::lsb_be(self.z_row, p - self.log_width)
        }
    }

    /// Evaluate `g_u(z_row, z_col, z_index, t_prev, t_next)` where `t_prev`
    /// and `t_next` are the column prefix sums encoded as length-m bit
    /// vectors over `F` (each entry must be 0 or 1).
    pub fn eval(&self, t_prev: &[F], t_next: &[F]) -> F {
        assert_eq!(t_prev.len(), self.log_dense_size);
        assert_eq!(t_next.len(), self.log_dense_size);
        assert_eq!(self.z_index.len(), self.log_dense_size);

        let states = all_states();

        // state_results[state_idx] = result of running BP from `state_idx` at
        // the current layer all the way to the sinks.
        let mut state_results: [F; W] = [F::ZERO; W];
        state_results[BpState::SUCCESS.idx()] = F::ONE;

        // Iterate from MSB layer (m-1) down to layer 0.
        for layer in (0..self.log_dense_size).rev() {
            let p = layer; // LSB position read at this layer

            let bits_eq = [
                self.row_bit(p),
                Self::lsb_be(self.z_col, p),
                Self::lsb_be(self.z_index, p),
                Self::lsb_be(t_prev, p),
                Self::lsb_be(t_next, p),
            ];

            // 32 weights, one per (row, col, idx, prev, next) ∈ {0,1}^5.
            let weights = eval_eq::<F>(&bits_eq);

            // Group transition outputs by (state, output_state).
            let mut transition_weight: [[F; W]; W] = [[F::ZERO; W]; W];
            for (combo_idx, &weight) in weights.iter().enumerate().take(N_BIT_COMBOS) {
                let combo = BitCombo::from_index(combo_idx);
                for &state in &states {
                    if let Some(next_state) = transition(state, combo) {
                        transition_weight[state.idx()][next_state.idx()] += weight;
                    }
                }
            }

            // new_state_results[s] = sum_{s'} transition_weight[s][s'] * state_results[s']
            let mut new_state_results: [F; W] = [F::ZERO; W];
            for s in 0..W {
                let mut acc = F::ZERO;
                for ss in 0..W {
                    acc += transition_weight[s][ss] * state_results[ss];
                }
                new_state_results[s] = acc;
            }
            state_results = new_state_results;
        }

        state_results[BpState::INITIAL.idx()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lean_vm::EF;
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    /// Direct integer evaluation of `g_u(row, col, idx, t_prev, t_next)`.
    fn g_direct(row: usize, col: usize, idx: usize, t_prev: usize, t_next: usize, log_width: usize) -> u8 {
        let lhs = t_prev + (row << log_width) + col;
        u8::from(lhs == idx && idx < t_next)
    }

    fn usize_to_be_bits<F: Field>(value: usize, n: usize) -> Vec<F> {
        let mut out = Vec::with_capacity(n);
        for i in (0..n).rev() {
            let bit = (value >> i) & 1;
            out.push(if bit == 1 { F::ONE } else { F::ZERO });
        }
        out
    }

    fn check_one(m: usize, u: usize, row: usize, col: usize, idx: usize, t_prev: usize, t_next: usize) {
        let n_row = m.saturating_sub(u);
        let n_col = u;
        let z_row = usize_to_be_bits::<EF>(row, n_row);
        let z_col = usize_to_be_bits::<EF>(col, n_col);
        let z_index = usize_to_be_bits::<EF>(idx, m);
        let t_prev_bits = usize_to_be_bits::<EF>(t_prev, m);
        let t_next_bits = usize_to_be_bits::<EF>(t_next, m);

        let bp = BranchingProgram {
            z_row: &z_row,
            z_col: &z_col,
            z_index: &z_index,
            log_width: u,
            log_dense_size: m,
        };
        let got = bp.eval(&t_prev_bits, &t_next_bits);
        let expected = g_direct(row, col, idx, t_prev, t_next, u);
        let expected_ef = if expected == 1 { EF::ONE } else { EF::ZERO };
        assert_eq!(
            got, expected_ef,
            "BP mismatch at m={m} u={u} row={row} col={col} idx={idx} t_prev={t_prev} t_next={t_next}",
        );
    }

    #[test]
    fn bp_matches_direct_random_samples() {
        let m = 8usize;
        for u in 0..=3usize {
            let n_row = m - u;
            let mut rng = StdRng::seed_from_u64(0xa55a_a55a + u as u64);
            for _ in 0..200 {
                let row: usize = rng.random_range(0..1 << n_row);
                let col: usize = if u == 0 { 0 } else { rng.random_range(0..1 << u) };
                let t_prev: usize = rng.random_range(0..1 << m);
                let t_next: usize = rng.random_range(0..1 << m);
                let idx: usize = rng.random_range(0..1 << m);
                check_one(m, u, row, col, idx, t_prev, t_next);
            }
        }
    }

    #[test]
    fn bp_matches_direct_satisfying_inputs() {
        let m = 8usize;
        for u in 0..=3usize {
            let mut rng = StdRng::seed_from_u64(0xdead_beef + u as u64);
            for _ in 0..100 {
                let n_row = m - u;
                let row: usize = rng.random_range(0..1 << n_row);
                let col: usize = if u == 0 { 0 } else { rng.random_range(0..1 << u) };
                let t_prev: usize = rng.random_range(0..(1 << m) - row * (1 << u) - col - 1).max(1);
                // Pick `t_next` strictly greater than `idx = t_prev + row*2^u + col`.
                let idx = t_prev + (row << u) + col;
                if idx >= (1 << m) {
                    continue;
                }
                let t_next = rng.random_range(idx + 1..=(1 << m) - 1);
                check_one(m, u, row, col, idx, t_prev, t_next);
                // The BP should output 1.
            }
        }
    }
}
