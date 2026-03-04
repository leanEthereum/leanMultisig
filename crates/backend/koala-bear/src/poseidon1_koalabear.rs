// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::sync::OnceLock;

use crate::KoalaBear;
use crate::symmetric::Permutation;
use field::{Algebra, InjectiveMonomial};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

pub const POSEIDON1_WIDTH: usize = 16;
pub const POSEIDON1_HALF_FULL_ROUNDS: usize = 4;
pub const POSEIDON1_PARTIAL_ROUNDS: usize = 20;
pub const POSEIDON1_SBOX_DEGREE: u64 = 3;

// =========================================================================
// Reed-Solomon MDS matrix (16x16) via coset-LDE
// =========================================================================

// Forward twiddles: W_k = omega^k.
const W1: KoalaBear = KoalaBear::new(0x08dbd69c);
const W2: KoalaBear = KoalaBear::new(0x6832fe4a);
const W3: KoalaBear = KoalaBear::new(0x27ae21e2);
const W4: KoalaBear = KoalaBear::new(0x7e010002); // omega^4, order 4
const W5: KoalaBear = KoalaBear::new(0x3a89a025);
const W6: KoalaBear = KoalaBear::new(0x174e3650);
const W7: KoalaBear = KoalaBear::new(0x27dfce22);

// Coset weights: WEIGHTS[i] = g^{bit_rev(i+1, 4)} for i=0..14.
// state[0] has weight g^0=1 so is skipped.
const WEIGHTS: [KoalaBear; 15] = KoalaBear::new_array([
    6_561,      // g^8
    81,         // g^4
    531_441,    // g^12
    9,          // g^2
    59_049,     // g^10
    729,        // g^6
    4_782_969,  // g^14
    3,          // g^1
    19_683,     // g^9
    243,        // g^5
    1_594_323,  // g^13
    27,         // g^3
    177_147,    // g^11
    2_187,      // g^7
    14_348_907, // g^15
]);

/// G_BR[j] = g^{bit_rev(j, 4)}.
const G_BR: [KoalaBear; 16] = KoalaBear::new_array([
    1, 6_561, 81, 531_441, 9, 59_049, 729, 4_782_969, 3, 19_683, 243, 1_594_323, 27, 177_147, 2_187, 14_348_907,
]);

/// NW_BR[j] = 16 * G_BR[j]. Multiplied into f_br each partial round to apply MDS.
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

/// sum(G_BR) = (3^16 - 1) / 2.
const SUM_G: KoalaBear = KoalaBear::new(21_523_360);

#[cfg(test)]
const N_INV: KoalaBear = KoalaBear::new(1_997_537_281); // 16^{-1} mod p

/// Cached IDFT_unnorm(partial_round_constants[k]) in bit-reversed order.
static PARTIAL_RC_F_CACHE: OnceLock<[[KoalaBear; 16]; POSEIDON1_PARTIAL_ROUNDS]> = OnceLock::new();

#[inline(never)]
fn partial_rc_f() -> &'static [[KoalaBear; 16]; POSEIDON1_PARTIAL_ROUNDS] {
    PARTIAL_RC_F_CACHE.get_or_init(|| {
        core::array::from_fn(|k| dif_ifft_16(&poseidon1_round_constants()[POSEIDON1_HALF_FULL_ROUNDS + k]))
    })
}

// =========================================================================
// Butterfly primitives
// =========================================================================

/// (lo, hi) -> (lo+hi, lo-hi).
#[inline(always)]
fn bt<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize) {
    let (a, b) = (v[lo], v[hi]);
    v[lo] = a + b;
    v[hi] = a - b;
}

/// DIT butterfly: (lo, hi) -> (lo + hi*t, lo - hi*t).
#[inline(always)]
fn dit<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize, t: KoalaBear) {
    let a = v[lo];
    let tb = v[hi] * t;
    v[lo] = a + tb;
    v[hi] = a - tb;
}

/// DIF butterfly with negated subtraction: (lo, hi) -> (lo+hi, (hi-lo)*t).
/// Exploits omega^{-k} = -omega^{8-k}: pass t = W_{8-k} instead of storing WI_k.
#[inline(always)]
fn neg_dif<R: Algebra<KoalaBear>>(v: &mut [R; 16], lo: usize, hi: usize, t: KoalaBear) {
    let (a, b) = (v[lo], v[hi]);
    v[lo] = a + b;
    v[hi] = (b - a) * t;
}

// =========================================================================
// 16-point FFT / IFFT (radix-2, fully unrolled, in-place)
// =========================================================================

/// DIF IFFT in-place: natural order -> bit-reversed frequency domain (unnormalized).
#[inline(always)]
fn dif_ifft_16_mut<R: Algebra<KoalaBear>>(f: &mut [R; 16]) {
    // Stage 1 — stride 8, inverse twiddles via neg_dif
    bt(f, 0, 8);
    neg_dif(f, 1, 9, W7);
    neg_dif(f, 2, 10, W6);
    neg_dif(f, 3, 11, W5);
    neg_dif(f, 4, 12, W4);
    neg_dif(f, 5, 13, W3);
    neg_dif(f, 6, 14, W2);
    neg_dif(f, 7, 15, W1);

    // Stage 2 — stride 4
    bt(f, 0, 4);
    neg_dif(f, 1, 5, W6);
    neg_dif(f, 2, 6, W4);
    neg_dif(f, 3, 7, W2);
    bt(f, 8, 12);
    neg_dif(f, 9, 13, W6);
    neg_dif(f, 10, 14, W4);
    neg_dif(f, 11, 15, W2);

    // Stage 3 — stride 2
    bt(f, 0, 2);
    neg_dif(f, 1, 3, W4);
    bt(f, 4, 6);
    neg_dif(f, 5, 7, W4);
    bt(f, 8, 10);
    neg_dif(f, 9, 11, W4);
    bt(f, 12, 14);
    neg_dif(f, 13, 15, W4);

    // Stage 4 — stride 1 (all twiddles = 1)
    bt(f, 0, 1);
    bt(f, 2, 3);
    bt(f, 4, 5);
    bt(f, 6, 7);
    bt(f, 8, 9);
    bt(f, 10, 11);
    bt(f, 12, 13);
    bt(f, 14, 15);
}

/// DIT FFT in-place: bit-reversed input -> natural order output.
#[inline(always)]
fn dit_fft_16_mut<R: Algebra<KoalaBear>>(f: &mut [R; 16]) {
    // Stage 1 — stride 1 (all twiddles = 1)
    bt(f, 0, 1);
    bt(f, 2, 3);
    bt(f, 4, 5);
    bt(f, 6, 7);
    bt(f, 8, 9);
    bt(f, 10, 11);
    bt(f, 12, 13);
    bt(f, 14, 15);

    // Stage 2 — stride 2
    bt(f, 0, 2);
    dit(f, 1, 3, W4);
    bt(f, 4, 6);
    dit(f, 5, 7, W4);
    bt(f, 8, 10);
    dit(f, 9, 11, W4);
    bt(f, 12, 14);
    dit(f, 13, 15, W4);

    // Stage 3 — stride 4
    bt(f, 0, 4);
    dit(f, 1, 5, W2);
    dit(f, 2, 6, W4);
    dit(f, 3, 7, W6);
    bt(f, 8, 12);
    dit(f, 9, 13, W2);
    dit(f, 10, 14, W4);
    dit(f, 11, 15, W6);

    // Stage 4 — stride 8
    bt(f, 0, 8);
    dit(f, 1, 9, W1);
    dit(f, 2, 10, W2);
    dit(f, 3, 11, W3);
    dit(f, 4, 12, W4);
    dit(f, 5, 13, W5);
    dit(f, 6, 14, W6);
    dit(f, 7, 15, W7);
}

/// Copying wrappers (used by permute_generic for frequency-domain entry/exit).
#[inline(always)]
fn dif_ifft_16<R: Algebra<KoalaBear>>(state: &[R; 16]) -> [R; 16] {
    let mut f = *state;
    dif_ifft_16_mut(&mut f);
    f
}

#[inline(always)]
fn dit_fft_16<R: Algebra<KoalaBear>>(state: &[R; 16]) -> [R; 16] {
    let mut f = *state;
    dit_fft_16_mut(&mut f);
    f
}

// =========================================================================
// MDS matrix application
// =========================================================================

/// Apply the 16x16 Reed-Solomon MDS: IFFT -> coset weights -> FFT.
/// Generic over any Algebra<KoalaBear> (scalar, SIMD-packed, extension field).
#[inline(always)]
pub fn mds_rs_16<R: Algebra<KoalaBear>>(state: &mut [R; 16]) {
    dif_ifft_16_mut(state);
    for i in 0..15 {
        state[i + 1] *= WEIGHTS[i];
    }
    dit_fft_16_mut(state);
}

// =========================================================================
// Poseidon1 permutation
// =========================================================================

#[derive(Clone, Debug)]
pub struct Poseidon1KoalaBear16 {}

#[inline(always)]
pub fn poseidon1_initial_constants() -> &'static [[KoalaBear; 16]] {
    &poseidon1_round_constants()[..POSEIDON1_HALF_FULL_ROUNDS]
}

#[inline(always)]
pub fn poseidon1_partial_constants() -> &'static [[KoalaBear; 16]] {
    &poseidon1_round_constants()[POSEIDON1_HALF_FULL_ROUNDS..POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS]
}

#[inline(always)]
pub fn poseidon1_final_constants() -> &'static [[KoalaBear; 16]] {
    &poseidon1_round_constants()[POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS..]
}

impl Poseidon1KoalaBear16 {
    /// Full Poseidon1 permutation with frequency-domain partial round optimization.
    #[inline(always)]
    #[allow(clippy::needless_range_loop)]
    fn permute_generic<R: Algebra<KoalaBear> + InjectiveMonomial<3>>(&self, state: &mut [R; 16]) {
        // Initial full rounds (all but last).
        for rc in &poseidon1_initial_constants()[..POSEIDON1_HALF_FULL_ROUNDS - 1] {
            Self::full_round(state, rc);
        }

        // Last initial full round: add_rc + S-box, then enter frequency domain
        // (skips the FFT/IFFT pair at the MDS/partial-round boundary).
        let rc_last = &poseidon1_initial_constants()[POSEIDON1_HALF_FULL_ROUNDS - 1];
        for (s, &c) in state.iter_mut().zip(rc_last.iter()) {
            *s += c;
        }
        for s in state.iter_mut() {
            *s = s.injective_exp_n();
        }

        // Partial rounds in frequency domain.
        //
        // Invariant: f_br[j] = NW_BR[j] * IDFT_unnorm(state)[bit_rev(j,4)]
        //            s0      = state[0] (time domain)
        //
        // Only state[0] gets the S-box; the MDS update on f_br is diagonal.
        {
            let rc_f = partial_rc_f();
            let g_br: [R; 16] = core::array::from_fn(|j| R::from(G_BR[j]));

            let mut f_br = dif_ifft_16(state);
            let mut s0 = R::dot_product::<16>(&f_br, &g_br);
            for j in 0..16 {
                f_br[j] *= NW_BR[j];
            }

            for (k, rc) in poseidon1_partial_constants().iter().enumerate() {
                // Add round constants in frequency domain.
                for j in 0..16 {
                    f_br[j] += rc_f[k][j];
                }
                let mut s0_prime = s0;
                s0_prime += rc[0];

                // S-box on state[0] only: delta = s0'^3 - s0'.
                let delta = s0_prime.injective_exp_n() - s0_prime;

                // New s0 via dot product, incorporating delta.
                s0 = R::dot_product::<16>(&f_br, &g_br);
                s0 += delta * SUM_G;

                // Add delta to all frequency bins, then apply MDS weights.
                for j in 0..16 {
                    f_br[j] += delta;
                }
                for j in 0..16 {
                    f_br[j] *= NW_BR[j];
                }
            }

            // Return to time domain: state = DIT_FFT(f_br) / 16.
            let dft_out = dit_fft_16(&f_br);
            for j in 0..16 {
                state[j] = dft_out[j].div_2exp_u64(4);
            }
        }

        // Final full rounds.
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
        mds_rs_16(state);
    }

    /// Sponge compression: state = permute(state) + state.
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

pub fn default_koalabear_poseidon1_16() -> Poseidon1KoalaBear16 {
    Poseidon1KoalaBear16 {}
}

// =========================================================================
// Round constants — generated from SmallRng::seed_from_u64(1)
// =========================================================================

const POSEIDON1_N_ROUNDS: usize = 2 * POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS;

static POSEIDON1_RC_CACHE: OnceLock<[[KoalaBear; 16]; POSEIDON1_N_ROUNDS]> = OnceLock::new();

pub fn poseidon1_round_constants() -> &'static [[KoalaBear; 16]; POSEIDON1_N_ROUNDS] {
    POSEIDON1_RC_CACHE.get_or_init(|| {
        let mut rng = SmallRng::seed_from_u64(1);
        core::array::from_fn(|_| core::array::from_fn(|_| rng.random()))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::KoalaBear;
    use field::PrimeCharacteristicRing;
    use field::PrimeField32;

    /// O(N^2) reference MDS for cross-checking.
    fn naive_rs_mds(input: &[KoalaBear; 16]) -> [KoalaBear; 16] {
        let omega = KoalaBear::new(0x08dbd69c);
        let omega_inv = KoalaBear::new(0x572031df);
        let g = KoalaBear::new(3);

        // Unnormalized IDFT
        let mut idft = [KoalaBear::ZERO; 16];
        for j in 0..16u64 {
            let wj = omega_inv.exp_u64(j);
            let mut w = KoalaBear::ONE;
            for k in 0..16 {
                idft[j as usize] += input[k] * w;
                w *= wj;
            }
        }

        // Coset shift
        let mut gj = KoalaBear::ONE;
        for v in idft.iter_mut() {
            *v *= gj;
            gj *= g;
        }

        // DFT
        let mut result = [KoalaBear::ZERO; 16];
        for m in 0..16u64 {
            let wm = omega.exp_u64(m);
            let mut w = KoalaBear::ONE;
            for j in 0..16 {
                result[m as usize] += idft[j] * w;
                w *= wm;
            }
        }
        result
    }

    /// Naive permutation using O(N^2) MDS — no FFT tricks.
    fn permute_naive(state: &mut [KoalaBear; 16]) {
        let full_round = |st: &mut [KoalaBear; 16], rc: &[KoalaBear; 16]| {
            for (s, &c) in st.iter_mut().zip(rc.iter()) {
                *s += c;
            }
            for s in st.iter_mut() {
                *s = s.injective_exp_n();
            }
            *st = naive_rs_mds(st);
        };
        let partial_round = |st: &mut [KoalaBear; 16], rc: &[KoalaBear; 16]| {
            for (s, &c) in st.iter_mut().zip(rc.iter()) {
                *s += c;
            }
            st[0] = st[0].injective_exp_n();
            *st = naive_rs_mds(st);
        };
        for rc in poseidon1_initial_constants() {
            full_round(state, rc);
        }
        for rc in poseidon1_partial_constants() {
            partial_round(state, rc);
        }
        for rc in poseidon1_final_constants() {
            full_round(state, rc);
        }
    }

    /// Reference permutation using mds_rs_16 (no freq-domain optimization).
    fn permute_reference(state: &mut [KoalaBear; 16]) {
        for rc in poseidon1_initial_constants() {
            Poseidon1KoalaBear16::full_round(state, rc);
        }
        for rc in poseidon1_partial_constants() {
            for (s, &c) in state.iter_mut().zip(rc.iter()) {
                *s += c;
            }
            state[0] = state[0].injective_exp_n();
            mds_rs_16(state);
        }
        for rc in poseidon1_final_constants() {
            Poseidon1KoalaBear16::full_round(state, rc);
        }
    }

    #[test]
    fn test_permutation_matches_naive() {
        let p1 = Poseidon1KoalaBear16 {};
        for seed in 0u32..50 {
            let state: [KoalaBear; 16] = core::array::from_fn(|i| KoalaBear::new(seed * 16 + i as u32 + 1));
            let mut opt = state;
            p1.permute_mut(&mut opt);
            let mut naive = state;
            permute_naive(&mut naive);
            assert_eq!(opt, naive, "seed={seed}");
        }
    }

    #[test]
    fn test_partial_rounds_fft_optimization() {
        let p1 = Poseidon1KoalaBear16 {};
        for seed in 0u32..50 {
            let state: [KoalaBear; 16] = core::array::from_fn(|i| KoalaBear::new(seed * 16 + i as u32 + 1));
            let mut opt = state;
            p1.permute_mut(&mut opt);
            let mut reference = state;
            permute_reference(&mut reference);
            assert_eq!(opt, reference, "seed={seed}");
        }
    }

    #[test]
    fn test_freq_domain_constants() {
        let g = KoalaBear::new(3);
        let n = KoalaBear::new(16);

        for j in 0u32..16 {
            let br = j.reverse_bits() >> 28;
            assert_eq!(G_BR[j as usize], g.exp_u64(br as u64));
        }
        for j in 0..16 {
            assert_eq!(NW_BR[j], n * G_BR[j]);
        }
        assert_eq!(SUM_G, G_BR.iter().copied().sum::<KoalaBear>());
        assert_eq!(N_INV * n, KoalaBear::ONE);

        let rc_f = partial_rc_f();
        for k in 0..POSEIDON1_PARTIAL_ROUNDS {
            let expected = dif_ifft_16(&poseidon1_round_constants()[POSEIDON1_HALF_FULL_ROUNDS + k]);
            assert_eq!(rc_f[k], expected);
        }
    }

    #[test]
    fn test_mds_rs_matches_naive() {
        for seed in 0u32..100 {
            let input: [KoalaBear; 16] = core::array::from_fn(|i| KoalaBear::new(seed * 16 + i as u32 + 1));
            let mut state = input;
            mds_rs_16(&mut state);
            assert_eq!(state, naive_rs_mds(&input), "seed={seed}");
        }
    }

    #[test]
    fn test_twiddle_constants() {
        let omega = KoalaBear::new(0x08dbd69c);
        let omega_inv = KoalaBear::new(0x572031df);
        let g = KoalaBear::new(3);

        // Forward twiddles
        for k in 1u64..=7 {
            let expected = omega.exp_u64(k);
            let actual = [W1, W2, W3, W4, W5, W6, W7][(k - 1) as usize];
            assert_eq!(actual, expected, "W{k}");
        }

        // omega^8 = -1, omega^16 = 1
        assert_eq!(omega.exp_u64(8), KoalaBear::NEG_ONE);
        assert_eq!(omega.exp_u64(16), KoalaBear::ONE);
        assert_eq!(omega * omega_inv, KoalaBear::ONE);

        // Negation identity: omega^{-k} = -omega^{8-k}
        for k in 1u64..=7 {
            assert_eq!(omega_inv.exp_u64(k), -omega.exp_u64(8 - k));
        }

        // Coset weights
        let bit_rev = [8u64, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15];
        for (i, &br) in bit_rev.iter().enumerate() {
            assert_eq!(WEIGHTS[i], g.exp_u64(br));
        }
    }

    #[test]
    fn test_plonky3_compatibility() {
        /*
                use p3_field::PrimeCharacteristicRing;
        use p3_mds::coset_mds::CosetMds;
        use p3_poseidon::{Poseidon, PoseidonExternalLayerGeneric, PoseidonInternalLayerGeneric};
        use p3_symmetric::Permutation;
        use rand::SeedableRng;
        use rand::rngs::SmallRng;

        use crate::KoalaBear;

        type Poseidon1KoalaBear16 = Poseidon<
            KoalaBear,
            PoseidonExternalLayerGeneric<KoalaBear, CosetMds<KoalaBear, 16>, 16>,
            PoseidonInternalLayerGeneric<KoalaBear, 16>,
            16,
            3,
        >;
        #[test]
        fn plonky3_test() {
            let mut rng = SmallRng::seed_from_u64(1);
            let half_num_full_rounds = 4;
            let num_partial_rounds = 20;
            let poseidon1 = Poseidon1KoalaBear16::new_from_rng(
                half_num_full_rounds,
                num_partial_rounds,
                &CosetMds::default(),
                &mut rng,
            );
            let mut zero_input = [KoalaBear::ZERO; 16];
            poseidon1.permute_mut(&mut zero_input);
            dbg!(&zero_input);
        }

        */
        let p1 = Poseidon1KoalaBear16 {};
        let mut state = [KoalaBear::ZERO; 16];
        p1.permute_mut(&mut state);
        let vals: Vec<u32> = state.iter().map(|x| x.as_canonical_u32()).collect();
        assert_eq!(
            vals,
            vec![
                601393743, 1019335148, 2037102651, 1805833401, 1439180585, 1479182195, 2033581729, 142725616,
                500833536, 1922045816, 1451656651, 1828439900, 1818330349, 494385058, 991888944, 486707181,
            ]
        );
    }
}
