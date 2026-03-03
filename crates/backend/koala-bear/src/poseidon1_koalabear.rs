// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::sync::OnceLock;

use crate::KoalaBear;
use crate::symmetric::Permutation;
use field::{Algebra, InjectiveMonomial};

pub const POSEIDON1_WIDTH: usize = 16;
pub const POSEIDON1_HALF_FULL_ROUNDS: usize = 4;
pub const POSEIDON1_PARTIAL_ROUNDS: usize = 20;
pub const POSEIDON1_SBOX_DEGREE: u64 = 3;

// ---------------------------------------------------------------------------
// Reed-Solomon (coset-LDE) 16×16 MDS for KoalaBear
//
// Computes: output = N · coset_LDE(input, shift = g)
//         = DFT( diag(g^j)_{j=0..15} · IDFT_unnorm(input) )
//
// where
//   ω   = primitive 16th root of unity  (TWO_ADIC_GENERATORS[4])
//   g   = 3  (multiplicative generator of KoalaBear*)
//
// Algorithm (fully unrolled, all indices compile-time constants):
//   Step 1  DIF IFFT with ω⁻¹ — 4 stages, output in bit-reversed order.
//   Step 2  Pointwise multiply by weights[i] = g^{bit_rev(i, 4)}.
//   Step 3  DIT  FFT with ω   — 4 stages, bit-reversed input → natural output.
//
// No allocation: all twiddles and weights are `const` field-element arrays.
//
// KEY IDENTITY: ω^{16-k} = ω^8 · ω^{8-k} = −ω^{8-k}, so
//   ω^{−k} = −ω^{8−k}   (k = 1..7)
// Therefore the 7 inverse twiddles WI_k = −W_{8−k} are NOT stored as separate
// constants.  Instead every DIF butterfly that would multiply by WI_k uses a
// `neg_dif` helper that subtracts in the opposite order and multiplies by W_{8-k}.
// This halves the twiddle constant pool (7 instead of 14), reducing register
// pressure on packed SIMD code.
//
// Operation count: 17 (IDFT) + 15 (weights) + 17 (DFT) = 49 R×KoalaBear muls.
// Butterflies with twiddle = 1 use plain add/sub (no multiplication).
// ---------------------------------------------------------------------------

// Forward twiddles ω^k (canonical form, k=0 → 1 handled by plain bt()).
const W1: KoalaBear = KoalaBear::new(0x08dbd69c); // ω¹
const W2: KoalaBear = KoalaBear::new(0x6832fe4a); // ω²
const W3: KoalaBear = KoalaBear::new(0x27ae21e2); // ω³
const W4: KoalaBear = KoalaBear::new(0x7e010002); // ω⁴  (primitive 4th root, ω⁴² = −1)
const W5: KoalaBear = KoalaBear::new(0x3a89a025); // ω⁵
const W6: KoalaBear = KoalaBear::new(0x174e3650); // ω⁶
const W7: KoalaBear = KoalaBear::new(0x27dfce22); // ω⁷

// Coset weights: WEIGHTS[i] = g^{bit_rev(i+1, 4)}, g = 3.
// (state[0] multiplied by g^0 = 1 → skipped; WEIGHTS[0] is for state[1].)
const WEIGHTS: [KoalaBear; 15] = KoalaBear::new_array([
    6_561,      // state[ 1] ← g^8
    81,         // state[ 2] ← g^4
    531_441,    // state[ 3] ← g^12
    9,          // state[ 4] ← g^2
    59_049,     // state[ 5] ← g^10
    729,        // state[ 6] ← g^6
    4_782_969,  // state[ 7] ← g^14
    3,          // state[ 8] ← g^1
    19_683,     // state[ 9] ← g^9
    243,        // state[10] ← g^5
    1_594_323,  // state[11] ← g^13
    27,         // state[12] ← g^3
    177_147,    // state[13] ← g^11
    2_187,      // state[14] ← g^7
    14_348_907, // state[15] ← g^15
]);

// ---------------------------------------------------------------------------
// Frequency-domain partial round optimization.
//
// The partial rounds (20 total) maintain f_br[j] = IDFT_unnorm(state)[bit_rev(j,4)]
// between rounds instead of applying the full MDS each time.
//
// Per partial round, the MDS update reduces to:
//   f_br_new[j] = NW_BR[j] * (f_br'[j] + delta)   [15 muls, NW_BR[0]=16 is 1 mul]
//   s0_new = dot(G_BR, f_br') + delta * SUM_G       [16 muls]
//   (vs 49 muls for the full MDS)
//
// Initialization: f_br = dif_ifft_16(state) [17 muls]
// Finalization:   state = dit_fft_16(f_br) / 16  [17+16 = 33 muls]
//
// Operation count per permutation:
//   4 full rounds (65 each) + IFFT init + 20 partial (34 each) + FFT fin + 4 full rounds
//   = 260 + 17 + 680 + 33 + 260 = 1250 muls  vs  1540 muls naive  (~19% faster)
// ---------------------------------------------------------------------------

/// g^{bit_rev(j, 4)} — same values as [1, WEIGHTS[0..14]].
const G_BR: [KoalaBear; 16] = KoalaBear::new_array([
    1, 6_561, 81, 531_441, 9, 59_049, 729, 4_782_969, 3, 19_683, 243, 1_594_323, 27, 177_147, 2_187, 14_348_907,
]);

/// N · g^{bit_rev(j, 4)}, N = 16.  Used to update f_br each partial round.
const NW_BR: [KoalaBear; 16] = KoalaBear::new_array([
    16,
    104_976,
    1_296,
    8_503_056,
    144,
    944_784,
    11_664,
    76_527_504,
    48,
    314_928,
    3_888,
    25_509_168,
    432,
    2_834_352,
    34_992,
    229_582_512,
]);

/// sum_{j=0}^{15} g^{bit_rev(j,4)} = (3^16 − 1)/2 = 21_523_360.
const SUM_G: KoalaBear = KoalaBear::new(21_523_360);

/// 16^{−1} mod p.  Since p = 16·133_169_152 + 1, we have 16^{-1} = p − 133_169_152.
#[cfg(test)]
const N_INV: KoalaBear = KoalaBear::new(1_997_537_281);

/// IDFT_unnorm(partial_RC[k])[bit_rev(j,4)] — cached on first use.
static PARTIAL_RC_F_CACHE: OnceLock<[[KoalaBear; 16]; POSEIDON1_PARTIAL_ROUNDS]> = OnceLock::new();

#[inline(never)]
fn partial_rc_f() -> &'static [[KoalaBear; 16]; POSEIDON1_PARTIAL_ROUNDS] {
    PARTIAL_RC_F_CACHE.get_or_init(|| {
        core::array::from_fn(|k| dif_ifft_16(&POSEIDON1_ROUND_CONSTANTS[POSEIDON1_HALF_FULL_ROUNDS + k]))
    })
}

// ---------------------------------------------------------------------------
// Butterfly helpers — take &mut [R;16] + compile-time index pairs.
// R: Algebra<KoalaBear> ⟹ R: Copy (via PrimeCharacteristicRing), so
// reading v[lo] and v[hi] copies the values before writing.
// ---------------------------------------------------------------------------

/// Plain butterfly (twiddle = 1): (lo, hi) → (lo+hi, lo−hi).
#[inline(always)]
fn bt<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize) {
    let (a, b) = (v[lo], v[hi]);
    v[lo] = a + b;
    v[hi] = a - b;
}

/// DIT butterfly: (lo, hi) → (lo + hi·t,  lo − hi·t).
#[inline(always)]
fn dit<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize, t: KoalaBear) {
    let a = v[lo];
    let tb = v[hi] * t;
    v[lo] = a + tb;
    v[hi] = a - tb;
}

/// DIF butterfly with **negated** subtraction order: (lo, hi) → (lo+hi, (hi−lo)·t).
///
/// Used in place of the standard DIF butterfly `(lo+hi, (lo−hi)·WI_k)` by
/// exploiting WI_k = −W_{8−k}, so `(lo−hi)·WI_k = (hi−lo)·W_{8−k}`.
///
/// This eliminates all 7 inverse-twiddle constants from the hot path.
#[inline(always)]
fn neg_dif<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize, t: KoalaBear) {
    let (a, b) = (v[lo], v[hi]);
    v[lo] = a + b;
    v[hi] = (b - a) * t; // (hi − lo) · t  ≡  (lo − hi) · (−t) = (lo − hi) · WI_{8−k}
}

/// DIF IFFT (4 stages): time-domain state → bit-reversed frequency domain.
/// Returns f_br where f_br[j] = IDFT_unnorm(state)[bit_rev(j, 4)].
#[inline(always)]
fn dif_ifft_16<R: Algebra<KoalaBear>>(state: &[R; 16]) -> [R; 16] {
    let mut f = *state;
    // Stage 1 — stride 8
    bt(&mut f, 0, 8);
    neg_dif(&mut f, 1, 9, W7);
    neg_dif(&mut f, 2, 10, W6);
    neg_dif(&mut f, 3, 11, W5);
    neg_dif(&mut f, 4, 12, W4);
    neg_dif(&mut f, 5, 13, W3);
    neg_dif(&mut f, 6, 14, W2);
    neg_dif(&mut f, 7, 15, W1);
    // Stage 2 — stride 4
    bt(&mut f, 0, 4);
    neg_dif(&mut f, 1, 5, W6);
    neg_dif(&mut f, 2, 6, W4);
    neg_dif(&mut f, 3, 7, W2);
    bt(&mut f, 8, 12);
    neg_dif(&mut f, 9, 13, W6);
    neg_dif(&mut f, 10, 14, W4);
    neg_dif(&mut f, 11, 15, W2);
    // Stage 3 — stride 2
    bt(&mut f, 0, 2);
    neg_dif(&mut f, 1, 3, W4);
    bt(&mut f, 4, 6);
    neg_dif(&mut f, 5, 7, W4);
    bt(&mut f, 8, 10);
    neg_dif(&mut f, 9, 11, W4);
    bt(&mut f, 12, 14);
    neg_dif(&mut f, 13, 15, W4);
    // Stage 4 — stride 1
    bt(&mut f, 0, 1);
    bt(&mut f, 2, 3);
    bt(&mut f, 4, 5);
    bt(&mut f, 6, 7);
    bt(&mut f, 8, 9);
    bt(&mut f, 10, 11);
    bt(&mut f, 12, 13);
    bt(&mut f, 14, 15);
    f
}

/// DIT FFT (4 stages): bit-reversed input → DFT output in natural order.
/// Computes DFT(f_nat) where f_nat[k] = f[bit_rev(k, 4)].
/// To recover state from f_br: state = dit_fft_16(&f_br) / 16.
#[inline(always)]
fn dit_fft_16<R: Algebra<KoalaBear>>(f: &[R; 16]) -> [R; 16] {
    let mut out = *f;
    // Stage 1 — stride 1
    bt(&mut out, 0, 1);
    bt(&mut out, 2, 3);
    bt(&mut out, 4, 5);
    bt(&mut out, 6, 7);
    bt(&mut out, 8, 9);
    bt(&mut out, 10, 11);
    bt(&mut out, 12, 13);
    bt(&mut out, 14, 15);
    // Stage 2 — stride 2
    bt(&mut out, 0, 2);
    dit(&mut out, 1, 3, W4);
    bt(&mut out, 4, 6);
    dit(&mut out, 5, 7, W4);
    bt(&mut out, 8, 10);
    dit(&mut out, 9, 11, W4);
    bt(&mut out, 12, 14);
    dit(&mut out, 13, 15, W4);
    // Stage 3 — stride 4
    bt(&mut out, 0, 4);
    dit(&mut out, 1, 5, W2);
    dit(&mut out, 2, 6, W4);
    dit(&mut out, 3, 7, W6);
    bt(&mut out, 8, 12);
    dit(&mut out, 9, 13, W2);
    dit(&mut out, 10, 14, W4);
    dit(&mut out, 11, 15, W6);
    // Stage 4 — stride 8
    bt(&mut out, 0, 8);
    dit(&mut out, 1, 9, W1);
    dit(&mut out, 2, 10, W2);
    dit(&mut out, 3, 11, W3);
    dit(&mut out, 4, 12, W4);
    dit(&mut out, 5, 13, W5);
    dit(&mut out, 6, 14, W6);
    dit(&mut out, 7, 15, W7);
    out
}

/// Apply the 16×16 Reed-Solomon MDS matrix.
///
/// Generic over `R: Algebra<KoalaBear>` — works for scalar KoalaBear, all packed
/// SIMD types, and extension field types without any type dispatch.
///
/// The inverse twiddles ω^{−k} = −ω^{8−k} are handled by `neg_dif` with forward
/// twiddles W_{8−k}, halving the constant pool and reducing register pressure on
/// packed SIMD code.
#[inline(always)]
pub fn mds_rs_16<R: Algebra<KoalaBear>>(state: &mut [R; 16]) {
    // ── Step 1: DIF IFFT — 4 stages, output in bit-reversed order ──
    //
    // Each DIF butterfly `(lo+hi, (lo−hi)·WI_k)` is replaced by
    // `neg_dif(lo, hi, W_{8−k})` using WI_k = −W_{8−k}.

    // Stage 1 — stride 8
    // Twiddles ω^{−j} for j=0..7.  Non-trivial: WI1=−W7 .. WI7=−W1.
    bt(state, 0, 8); // j=0: twiddle=1
    neg_dif(state, 1, 9, W7); // j=1: WI1 = −W7
    neg_dif(state, 2, 10, W6); // j=2: WI2 = −W6
    neg_dif(state, 3, 11, W5); // j=3: WI3 = −W5
    neg_dif(state, 4, 12, W4); // j=4: WI4 = −W4
    neg_dif(state, 5, 13, W3); // j=5: WI5 = −W3
    neg_dif(state, 6, 14, W2); // j=6: WI6 = −W2
    neg_dif(state, 7, 15, W1); // j=7: WI7 = −W1

    // Stage 2 — stride 4, twiddles ω^{−2j}, two blocks of 8
    bt(state, 0, 4); // block 0, j=0
    neg_dif(state, 1, 5, W6); // j=1: WI2 = −W6
    neg_dif(state, 2, 6, W4); // j=2: WI4 = −W4
    neg_dif(state, 3, 7, W2); // j=3: WI6 = −W2
    bt(state, 8, 12); // block 1, j=0
    neg_dif(state, 9, 13, W6); // j=1
    neg_dif(state, 10, 14, W4); // j=2
    neg_dif(state, 11, 15, W2); // j=3

    // Stage 3 — stride 2, twiddle ω^{−4}, four blocks of 4
    bt(state, 0, 2);
    neg_dif(state, 1, 3, W4); // WI4 = −W4
    bt(state, 4, 6);
    neg_dif(state, 5, 7, W4);
    bt(state, 8, 10);
    neg_dif(state, 9, 11, W4);
    bt(state, 12, 14);
    neg_dif(state, 13, 15, W4);

    // Stage 4 — stride 1, all twiddles = 1 → 8 plain butterflies
    bt(state, 0, 1);
    bt(state, 2, 3);
    bt(state, 4, 5);
    bt(state, 6, 7);
    bt(state, 8, 9);
    bt(state, 10, 11);
    bt(state, 12, 13);
    bt(state, 14, 15);

    // ── Step 2: multiply by coset weights  weights[i] = g^{bit_rev(i,4)} ──
    // state[0] *= g^0 = 1  →  skipped
    state[1] *= WEIGHTS[0]; // g^8
    state[2] *= WEIGHTS[1]; // g^4
    state[3] *= WEIGHTS[2]; // g^12
    state[4] *= WEIGHTS[3]; // g^2
    state[5] *= WEIGHTS[4]; // g^10
    state[6] *= WEIGHTS[5]; // g^6
    state[7] *= WEIGHTS[6]; // g^14
    state[8] *= WEIGHTS[7]; // g^1
    state[9] *= WEIGHTS[8]; // g^9
    state[10] *= WEIGHTS[9]; // g^5
    state[11] *= WEIGHTS[10]; // g^13
    state[12] *= WEIGHTS[11]; // g^3
    state[13] *= WEIGHTS[12]; // g^11
    state[14] *= WEIGHTS[13]; // g^7
    state[15] *= WEIGHTS[14]; // g^15

    // ── Step 3: DIT FFT — bit-reversed input → natural order output ──

    // Stage 1 — stride 1, all twiddles = 1
    bt(state, 0, 1);
    bt(state, 2, 3);
    bt(state, 4, 5);
    bt(state, 6, 7);
    bt(state, 8, 9);
    bt(state, 10, 11);
    bt(state, 12, 13);
    bt(state, 14, 15);

    // Stage 2 — stride 2, twiddle ω^4, four blocks of 4
    bt(state, 0, 2);
    dit(state, 1, 3, W4);
    bt(state, 4, 6);
    dit(state, 5, 7, W4);
    bt(state, 8, 10);
    dit(state, 9, 11, W4);
    bt(state, 12, 14);
    dit(state, 13, 15, W4);

    // Stage 3 — stride 4, twiddles ω^{2j}, two blocks of 8
    bt(state, 0, 4); // block 0, j=0
    dit(state, 1, 5, W2);
    dit(state, 2, 6, W4);
    dit(state, 3, 7, W6);
    bt(state, 8, 12); // block 1, j=0
    dit(state, 9, 13, W2);
    dit(state, 10, 14, W4);
    dit(state, 11, 15, W6);

    // Stage 4 — stride 8, twiddles ω^j for j=0..7
    bt(state, 0, 8); // j=0: twiddle=1
    dit(state, 1, 9, W1);
    dit(state, 2, 10, W2);
    dit(state, 3, 11, W3);
    dit(state, 4, 12, W4);
    dit(state, 5, 13, W5);
    dit(state, 6, 14, W6);
    dit(state, 7, 15, W7);
}

/// The Poseidon1 permutation for KoalaBear, width 16, cube S-box.
#[derive(Clone, Debug)]
pub struct Poseidon1KoalaBear16 {}

/// Get constants for initial full rounds (first 4 rounds).
#[inline(always)]
pub fn poseidon1_initial_constants() -> &'static [[KoalaBear; 16]] {
    &POSEIDON1_ROUND_CONSTANTS[..POSEIDON1_HALF_FULL_ROUNDS]
}

/// Get constants for partial rounds (middle 20 rounds).
#[inline(always)]
pub fn poseidon1_partial_constants() -> &'static [[KoalaBear; 16]] {
    &POSEIDON1_ROUND_CONSTANTS[POSEIDON1_HALF_FULL_ROUNDS..POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS]
}

/// Get constants for final full rounds (last 4 rounds).
#[inline(always)]
pub fn poseidon1_final_constants() -> &'static [[KoalaBear; 16]] {
    &POSEIDON1_ROUND_CONSTANTS[POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS..]
}

impl Poseidon1KoalaBear16 {
    /// Apply the permutation to a state, works generically on any Algebra<KoalaBear>.
    ///
    /// Partial rounds use the frequency-domain optimisation: maintains
    /// f_br[j] = IDFT_unnorm(state)[bit_rev(j,4)] between rounds, reducing each
    /// partial round from 49 MDS multiplications to 31 (15 for f update + 16 for s0).
    #[inline(always)]
    fn permute_generic<R: Algebra<KoalaBear> + InjectiveMonomial<3>>(&self, state: &mut [R; 16]) {
        // ── Initial full rounds ──────────────────────────────────────────────
        for rc in poseidon1_initial_constants() {
            Self::full_round(state, rc);
        }

        // ── Partial rounds (frequency-domain) ───────────────────────────────
        //
        // Invariant: f_br[j] = IDFT_unnorm(state)[bit_rev(j,4)]
        //            s0      = state[0]  (time-domain)
        //
        // Per round:
        //   1. f_br'[j]  = f_br[j] + IDFT_unnorm(RC[k])[bit_rev(j,4)]       (adds)
        //   2. delta     = (s0 + RC[k,0])^3 − (s0 + RC[k,0])                (2 muls)
        //   3. s0_new    = dot(G_BR, f_br') + delta · SUM_G                  (16 muls)
        //   4. f_br''[j] = f_br'[j] + delta                                  (adds)
        //   5. f_br_new[j] = NW_BR[j] · f_br''[j]                           (16 muls)
        {
            let rc_f = partial_rc_f();
            let mut f_br = dif_ifft_16(state);
            let mut s0 = state[0];

            for (k, rc) in poseidon1_partial_constants().iter().enumerate() {
                // Step 1: add round constant in frequency domain.
                for j in 0..16 {
                    f_br[j] += rc_f[k][j];
                }
                let mut s0_prime = s0;
                s0_prime += rc[0];

                // Step 2: S-box on time-domain state[0].
                let cube = s0_prime.injective_exp_n(); // s0'^3
                let delta = cube - s0_prime; // delta = s0'^3 − s0'

                // Step 3: s0_new = sum_j G_BR[j] * f_br'[j]  +  delta * SUM_G
                //         (uses f_br' = f_br AFTER step 1, BEFORE steps 4–5)
                s0 = f_br[0]; // G_BR[0] = 1
                for j in 1..16 {
                    s0 += f_br[j] * G_BR[j];
                }
                s0 += delta * SUM_G;

                // Step 4: add delta to all frequency bins.
                for j in 0..16 {
                    f_br[j] += delta;
                }

                // Step 5: multiply by NW_BR (= N * g^{bit_rev(j,4)}) to complete MDS.
                for j in 0..16 {
                    f_br[j] *= NW_BR[j];
                }
            }
            let _ = s0; // last value unused; LLVM eliminates it

            // Recover time-domain state:  state = DIT_FFT(f_br) / N
            let dft_out = dit_fft_16(&f_br);
            for j in 0..16 {
                state[j] = dft_out[j].div_2exp_u64(4); // ÷16
            }
        }

        // ── Final full rounds ────────────────────────────────────────────────
        for rc in poseidon1_final_constants() {
            Self::full_round(state, rc);
        }
    }

    /// A full round: add constants to all elements, cube all elements, apply MDS.
    #[inline(always)]
    fn full_round<R: Algebra<KoalaBear> + InjectiveMonomial<3>>(state: &mut [R; 16], rc: &[KoalaBear; 16]) {
        for (s, &c) in state.iter_mut().zip(rc.iter()) {
            *s += c;
        }
        for s in state.iter_mut() {
            *s = s.injective_exp_n();
        }
        mds_rs_16(state);
    }

    /// Compression: output = perm(input) + input
    #[inline(always)]
    pub fn compress_in_place<R: Algebra<KoalaBear> + InjectiveMonomial<3>>(&self, state: &mut [R; 16]) {
        let initial = *state;
        self.permute_generic(state);
        for (s, init) in state.iter_mut().zip(initial) {
            *s += init;
        }
    }
}

impl<R: Algebra<KoalaBear> + InjectiveMonomial<3> + Send + Sync> Permutation<[R; 16]> for Poseidon1KoalaBear16 {
    fn permute_mut(&self, input: &mut [R; 16]) {
        self.permute_generic(input);
    }
}

// ---------------------------------------------------------------------------
// Round constants (pseudo-random, generated from a seeded LCG).
// Regenerate with: cargo test -p mt-koala-bear -- generate_poseidon1_constants --ignored --nocapture
// ---------------------------------------------------------------------------

const POSEIDON1_N_ROUNDS: usize = 2 * POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS;

pub const POSEIDON1_ROUND_CONSTANTS: [[KoalaBear; 16]; POSEIDON1_N_ROUNDS] = KoalaBear::new_2d_array([
    [
        216749373, 1820772958, 1683239962, 557120727, 1095002112, 2125582037, 737197768, 1102422328, 873311853,
        2033676758, 1651676783, 615033470, 836368007, 528067299, 664765641, 1945310295,
    ],
    [
        1514248089, 310184232, 1641667373, 492677126, 651940972, 1742733370, 700161995, 81280490, 310447354, 487263886,
        977757844, 1213159012, 1982108473, 1854521200, 583869203, 1290970207,
    ],
    [
        938704579, 746780521, 401887696, 1448362595, 1362744957, 1999281219, 1265364854, 502975266, 91193715,
        843555671, 467672053, 1922312593, 163305482, 826203318, 1931713216, 14798914,
    ],
    [
        734606174, 816047602, 778218551, 2072007162, 3018054, 1464474467, 532520690, 65595155, 775986078, 1810656310,
        146817614, 1910794041, 698663738, 1010518094, 2079799856, 1007333670,
    ],
    [
        1485202113, 332853, 374352629, 205847050, 1012409714, 1931992897, 478671759, 1592707994, 875005364, 184480624,
        1897991091, 197467689, 351479176, 2010942007, 1031096282, 459599701,
    ],
    [
        171607928, 1158496650, 51370539, 277411057, 732733354, 358529549, 200545454, 1400455033, 1307225716, 668117792,
        893229130, 1042397630, 476275275, 709863253, 1603104598, 836850136,
    ],
    [
        1620084246, 106213799, 1090533354, 1106485200, 1546841463, 862202037, 670511104, 1273209339, 1569893860,
        257307460, 389092722, 1635319780, 16207944, 777804792, 1765087474, 1406924741,
    ],
    [
        872903413, 258178792, 1938016836, 291206791, 490406192, 233357935, 1499112600, 1205426050, 71780647,
        1488451268, 1071066331, 670378659, 1138911184, 165587212, 267103325, 68145579,
    ],
    [
        1311405394, 1088795831, 264547722, 1511849587, 754355552, 1501167650, 783795538, 1146387831, 418486787,
        2041145841, 1806457876, 992635828, 656640658, 620078682, 612753127, 1488884145,
    ],
    [
        1389485134, 700861634, 1858749255, 1286848119, 358109235, 194190884, 1735385856, 1943039029, 1012039290,
        1269159173, 1749085451, 1179502753, 1602539969, 228994148, 1559055819, 134277338,
    ],
    [
        1798543951, 1167313248, 4278883, 754549459, 1364846439, 1259764442, 1892970237, 1689988428, 1125946644,
        1692874001, 1903060984, 1463082479, 844885741, 353339488, 1756415251, 1767606262,
    ],
    [
        84769604, 1688913842, 1916258557, 2028129090, 2102315319, 2040296613, 40248955, 109948088, 1011427903,
        371285493, 1763997506, 2002106318, 1901055018, 89656520, 838382470, 180746942,
    ],
    [
        1786743370, 1055163395, 2063028345, 1953096162, 733552340, 1864395193, 860706617, 1714883459, 1498389337,
        78718913, 122639828, 2035060442, 1352284143, 203878662, 934439988, 1648956306,
    ],
    [
        1010907959, 1911614170, 1259947064, 2023536997, 1043029204, 1834490941, 15756793, 582228553, 1360974804,
        1907036701, 722403426, 19126115, 2058783036, 383292089, 1653339653, 356204143,
    ],
    [
        297274493, 739602764, 2028596106, 1215058192, 421500457, 493706582, 1591287633, 750821935, 1605937415,
        52062245, 489914910, 263827898, 909133956, 496618262, 1722370533, 753512830,
    ],
    [
        1394243070, 2093190919, 1697658704, 535756030, 1951639070, 870678908, 485202769, 176997053, 622262551,
        265260863, 129488232, 505702928, 1733233107, 322874079, 30605312, 1210978783,
    ],
    [
        1798707509, 811291797, 511263692, 1010929974, 690449865, 893239480, 1280203888, 1011174183, 1083347334,
        961661806, 1489105126, 1726371418, 850314427, 989368187, 54365321, 1409860364,
    ],
    [
        1386497861, 897071194, 353877800, 1159073279, 2008056208, 1680295215, 1598308951, 705336702, 2086404581,
        1155949468, 1803794834, 571998403, 158209663, 1560748958, 1492077729, 2094577526,
    ],
    [
        1463030127, 1247270093, 2032172334, 1464405001, 196395808, 978930318, 514181364, 1638271559, 280403748,
        1579462752, 1479914043, 23997729, 1971190534, 304053783, 825934783, 1211250883,
    ],
    [
        34945120, 306442858, 1322164398, 2072626903, 1451459699, 144920785, 1251560552, 65737478, 1519262732,
        1966882746, 1749639417, 1797777402, 382249226, 2089562412, 1723435576, 111590963,
    ],
    [
        1071345390, 795531229, 383968027, 523977726, 1538453582, 340067552, 1705339455, 1093984808, 917453649,
        2062014547, 249463564, 427781525, 1784110603, 536395034, 1018400081, 1997047741,
    ],
    [
        281380007, 255490793, 1237492440, 976729505, 387814600, 1486168455, 1396420735, 1407129310, 1818509260,
        235259559, 561727416, 690968460, 760809095, 2003990566, 988111208, 1943360580,
    ],
    [
        802172116, 941935754, 1196720312, 873060032, 1813646414, 380382024, 795142920, 820765536, 292937559,
        2096332476, 335866503, 251404146, 2028850924, 1181261523, 203916968, 1098656134,
    ],
    [
        1845507662, 296549067, 886666541, 1619173327, 1523376559, 723224971, 642482116, 1413938202, 2023333065,
        18365632, 1593517450, 737715449, 317049303, 1197268645, 1972347097, 2065876007,
    ],
    [
        385624255, 1287594718, 4875689, 407654933, 1252191138, 1437933474, 704342573, 1228486209, 1814465939,
        260042545, 705041404, 342558254, 1697839115, 595938825, 490980026, 359130739,
    ],
    [
        914447296, 1016958441, 1309893309, 272529498, 1383627860, 1393240107, 1154647710, 44915798, 327266182,
        939873525, 150683114, 1607317556, 464068274, 1675125714, 996085101, 1700813890,
    ],
    [
        628931677, 304100109, 291428176, 734075732, 1236263288, 1956361544, 29818369, 1809538832, 1276318511,
        256891374, 1083942204, 1265069838, 264763481, 668672206, 1173750908, 2008361606,
    ],
    [
        60003701, 2107431208, 1921257897, 629147757, 1535103317, 1703860279, 182239811, 2060167474, 1488797538,
        1087855756, 1416744121, 1717240562, 1857449266, 990985724, 92280553, 844759303,
    ],
]);

/// Create a default Poseidon1 instance for KoalaBear width 16.
pub fn default_koalabear_poseidon1_16() -> Poseidon1KoalaBear16 {
    Poseidon1KoalaBear16 {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::KoalaBear;
    use field::{PrimeCharacteristicRing, PrimeField32};

    /// Regenerate and verify the POSEIDON1_ROUND_CONSTANTS array.
    /// Run with: cargo test -p mt-koala-bear -- generate_poseidon1_constants --ignored --nocapture
    #[test]
    #[ignore]
    fn generate_poseidon1_constants() {
        const P: u64 = 2130706433;
        const TOTAL: usize = POSEIDON1_N_ROUNDS * 16;

        let mut state: u64 = 0x506F736569646F6E; // "Poseidon" as seed
        let a: u64 = 6364136223846793005;
        let c: u64 = 1442695040888963407;

        let mut values = alloc::vec::Vec::with_capacity(TOTAL);
        for _ in 0..TOTAL {
            state = state.wrapping_mul(a).wrapping_add(c);
            let val = (state >> 33) % P;
            values.push(KoalaBear::new(val as u32));
        }

        // Verify the hardcoded constants match
        for (round, chunk) in values.chunks_exact(16).enumerate() {
            for (j, &v) in chunk.iter().enumerate() {
                assert_eq!(
                    POSEIDON1_ROUND_CONSTANTS[round][j], v,
                    "Mismatch at round={round}, index={j}"
                );
            }
        }

        // Print the const array for copy-pasting
        println!(
            "const POSEIDON1_ROUND_CONSTANTS: [[KoalaBear; 16]; {POSEIDON1_N_ROUNDS}] = KoalaBear::new_2d_array(["
        );
        for chunk in values.chunks_exact(16) {
            let vals: alloc::vec::Vec<_> = chunk.iter().map(|v| v.as_canonical_u32().to_string()).collect();
            println!("    [{}],", vals.join(", "));
        }
        println!("]);");
    }

    /// Naive reference implementation of the RS-MDS via explicit O(N²) IDFT + weight + DFT.
    fn naive_rs_mds(input: &[KoalaBear; 16]) -> [KoalaBear; 16] {
        let omega = KoalaBear::new(0x08dbd69c); // primitive 16th root ω
        let omega_inv = KoalaBear::new(0x572031df); // ω⁻¹
        let g = KoalaBear::new(3); // multiplicative generator

        // Step 1: N · IDFT(input)  [unnormalized, O(N²)]
        let mut idft = [KoalaBear::ZERO; 16];
        for j in 0..16u64 {
            let wj = omega_inv.exp_u64(j); // ω^{−j}
            let mut w = KoalaBear::ONE;
            let mut sum = KoalaBear::ZERO;
            for k in 0..16 {
                sum += input[k] * w;
                w *= wj;
            }
            idft[j as usize] = sum;
        }

        // Step 2: multiply by g^j
        let mut gj = KoalaBear::ONE;
        for j in 0..16 {
            idft[j] *= gj;
            gj *= g;
        }

        // Step 3: DFT(idft)  [O(N²)]
        let mut result = [KoalaBear::ZERO; 16];
        for m in 0..16u64 {
            let wm = omega.exp_u64(m); // ω^m
            let mut w = KoalaBear::ONE;
            let mut sum = KoalaBear::ZERO;
            for j in 0..16 {
                sum += idft[j] * w;
                w *= wm;
            }
            result[m as usize] = sum;
        }
        result
    }

    /// Fully naive permutation: every MDS computed via the O(N²) coset-LDE.
    /// No FFT, no SIMD — just schoolbook IDFT + weight + DFT.
    fn permute_naive(state: &mut [KoalaBear; 16]) {
        let naive_full_round = |st: &mut [KoalaBear; 16], rc: &[KoalaBear; 16]| {
            for (s, &c) in st.iter_mut().zip(rc.iter()) {
                *s += c;
            }
            for s in st.iter_mut() {
                *s = s.injective_exp_n();
            }
            *st = naive_rs_mds(st);
        };
        let naive_partial_round = |st: &mut [KoalaBear; 16], rc: &[KoalaBear; 16]| {
            for (s, &c) in st.iter_mut().zip(rc.iter()) {
                *s += c;
            }
            st[0] = st[0].injective_exp_n();
            *st = naive_rs_mds(st);
        };
        for rc in poseidon1_initial_constants() {
            naive_full_round(state, rc);
        }
        for rc in poseidon1_partial_constants() {
            naive_partial_round(state, rc);
        }
        for rc in poseidon1_final_constants() {
            naive_full_round(state, rc);
        }
    }

    /// End-to-end equivalence: optimised permutation == fully naive O(N²) permutation.
    ///
    /// This closes the verification chain without relying on mds_rs_16 correctness:
    /// permute_mut (freq-domain optimised) == permute_naive (schoolbook IDFT/DFT for every MDS).
    #[test]
    fn test_permutation_matches_naive() {
        let p1 = Poseidon1KoalaBear16 {};
        for seed in 0u32..50 {
            let state: [KoalaBear; 16] = core::array::from_fn(|i| KoalaBear::new(seed * 16 + i as u32 + 1));
            let mut opt = state;
            p1.permute_mut(&mut opt);
            let mut naive = state;
            permute_naive(&mut naive);
            assert_eq!(opt, naive, "Mismatch at seed={seed}");
        }
    }

    /// Reference (non-freq-domain) permutation using mds_rs_16 directly.
    fn permute_reference(state: &mut [KoalaBear; 16]) {
        let partial_round = |st: &mut [KoalaBear; 16], rc: &[KoalaBear; 16]| {
            for (s, &c) in st.iter_mut().zip(rc.iter()) {
                *s += c;
            }
            st[0] = st[0].injective_exp_n();
            mds_rs_16(st);
        };
        for rc in poseidon1_initial_constants() {
            Poseidon1KoalaBear16::full_round(state, rc);
        }
        for rc in poseidon1_partial_constants() {
            partial_round(state, rc);
        }
        for rc in poseidon1_final_constants() {
            Poseidon1KoalaBear16::full_round(state, rc);
        }
    }

    /// Verify the frequency-domain partial round optimisation matches the mds_rs_16 path.
    #[test]
    fn test_partial_rounds_fft_optimization() {
        let p1 = Poseidon1KoalaBear16 {};
        for seed in 0u32..50 {
            let state: [KoalaBear; 16] = core::array::from_fn(|i| KoalaBear::new(seed * 16 + i as u32 + 1));
            let mut opt = state;
            p1.permute_mut(&mut opt);
            let mut reference = state;
            permute_reference(&mut reference);
            assert_eq!(opt, reference, "Mismatch at seed={seed}");
        }
    }

    /// Verify the new constants are consistent with the field arithmetic.
    #[test]
    fn test_freq_domain_constants() {
        let g = KoalaBear::new(3);
        let n = KoalaBear::new(16);

        // G_BR[j] = g^{bit_rev(j,4)}
        for j in 0u32..16 {
            let br = j.reverse_bits() >> 28; // 4-bit reversal
            assert_eq!(G_BR[j as usize], g.exp_u64(br as u64), "G_BR[{j}]");
        }

        // NW_BR[j] = N * G_BR[j]
        for j in 0..16 {
            assert_eq!(NW_BR[j], n * G_BR[j], "NW_BR[{j}]");
        }

        // SUM_G = (3^16 - 1)/2 = 21_523_360
        let sum: KoalaBear = G_BR.iter().copied().sum();
        assert_eq!(SUM_G, sum);

        // N_INV * 16 = 1
        assert_eq!(N_INV * KoalaBear::new(16), KoalaBear::ONE);

        // PARTIAL_RC_F[k] = dif_ifft_16(partial_RC[k])
        let rc_f = partial_rc_f();
        for k in 0..POSEIDON1_PARTIAL_ROUNDS {
            let expected = dif_ifft_16(&POSEIDON1_ROUND_CONSTANTS[POSEIDON1_HALF_FULL_ROUNDS + k]);
            assert_eq!(rc_f[k], expected, "PARTIAL_RC_F[{k}]");
        }
    }

    /// Cross-check mds_rs_16 against the naive coset-LDE reference.
    #[test]
    fn test_mds_rs_matches_naive() {
        for seed in 0u32..100 {
            let input: [KoalaBear; 16] = core::array::from_fn(|i| KoalaBear::new(seed * 16 + i as u32 + 1));
            let mut state = input;
            mds_rs_16(&mut state);
            let expected = naive_rs_mds(&input);
            assert_eq!(state, expected, "Mismatch at seed={seed}");
        }
    }

    /// Verify W1–W7, their negation identity WI_k = −W_{8−k}, and WEIGHTS.
    #[test]
    fn test_rs_mds_constants() {
        let omega = KoalaBear::new(0x08dbd69c);

        // Forward twiddles: ω^k
        assert_eq!(W1, omega.exp_u64(1));
        assert_eq!(W2, omega.exp_u64(2));
        assert_eq!(W3, omega.exp_u64(3));
        assert_eq!(W4, omega.exp_u64(4));
        assert_eq!(W5, omega.exp_u64(5));
        assert_eq!(W6, omega.exp_u64(6));
        assert_eq!(W7, omega.exp_u64(7));

        // ω^8 = −1  (W4 has order 4: W4² = ω^8 = −1)
        assert_eq!(omega.exp_u64(8), KoalaBear::NEG_ONE);
        assert_eq!(W4.exp_u64(4), KoalaBear::ONE);
        assert_ne!(W4.exp_u64(2), KoalaBear::ONE);

        // Negation identity: WI_k = −W_{8−k}
        let omega_inv = KoalaBear::new(0x572031df);
        assert_eq!(omega_inv.exp_u64(1), -W7, "WI1 ≠ −W7");
        assert_eq!(omega_inv.exp_u64(2), -W6, "WI2 ≠ −W6");
        assert_eq!(omega_inv.exp_u64(3), -W5, "WI3 ≠ −W5");
        assert_eq!(omega_inv.exp_u64(4), -W4, "WI4 ≠ −W4");
        assert_eq!(omega_inv.exp_u64(5), -W3, "WI5 ≠ −W3");
        assert_eq!(omega_inv.exp_u64(6), -W2, "WI6 ≠ −W2");
        assert_eq!(omega_inv.exp_u64(7), -W1, "WI7 ≠ −W1");

        // omega * omega_inv = 1
        assert_eq!(omega * omega_inv, KoalaBear::ONE);
        // omega^16 = 1
        assert_eq!(omega.exp_u64(16), KoalaBear::ONE);

        // Weights: g^{bit_rev(i, 4)} for i = 1..15
        let g = KoalaBear::new(3);
        // bit_rev(1,4) = 8, bit_rev(2,4) = 4, bit_rev(3,4) = 12, ...
        let bit_rev = [8u64, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15];
        for (i, &br) in bit_rev.iter().enumerate() {
            assert_eq!(WEIGHTS[i], g.exp_u64(br), "WEIGHTS[{i}] mismatch");
        }
    }
}
