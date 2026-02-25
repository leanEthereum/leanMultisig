//! Poseidon1 permutation for KoalaBear, WIDTH=16, ALPHA=3 (cube S-box).
//!
//! Uses the BabyBear circulant MDS matrix for all rounds (both full and partial).
//! Round structure: 4 initial full rounds + 20 partial rounds + 4 final full rounds.

use std::any::TypeId;

use crate::symmetric::Permutation;
use crate::{KoalaBear, KoalaBearParameters, MontyParameters};
use field::{Algebra, InjectiveMonomial, PrimeCharacteristicRing};

pub const POSEIDON1_WIDTH: usize = 16;
pub const POSEIDON1_HALF_FULL_ROUNDS: usize = 4;
pub const POSEIDON1_PARTIAL_ROUNDS: usize = 20;
pub const POSEIDON1_SBOX_DEGREE: u64 = 3;

/// First row of the 16x16 circulant MDS matrix (same as BabyBear).
pub const MDS_CIRC_16_FIRST_ROW: [u64; 16] = [1, 1, 51, 1, 11, 17, 2, 1, 101, 63, 15, 2, 67, 22, 13, 3];

/// First column of the circulant MDS matrix (element 0 stays, elements 1..16 reversed).
/// Used by the Karatsuba convolution fast path.
const MDS_CIRC_16_FIRST_COL: [i64; 16] = [1, 3, 13, 22, 67, 2, 15, 63, 101, 1, 2, 17, 11, 1, 51, 1];

// ---------------------------------------------------------------------------
// Karatsuba convolution for KoalaBear MDS (i64 fast path)
// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).
// ---------------------------------------------------------------------------

#[inline(always)]
fn dot_product_i64<const N: usize>(u: [i64; N], v: [i64; N]) -> i64 {
    let mut dp = u[0] * v[0];
    for i in 1..N {
        dp += u[i] * v[i];
    }
    dp
}

#[inline(always)]
fn negacyclic_conv4_i64(lhs: [i64; 4], rhs: [i64; 4], output: &mut [i64; 4]) {
    output[0] = dot_product_i64(lhs, [rhs[0], -rhs[3], -rhs[2], -rhs[1]]);
    output[1] = dot_product_i64(lhs, [rhs[1], rhs[0], -rhs[3], -rhs[2]]);
    output[2] = dot_product_i64(lhs, [rhs[2], rhs[1], rhs[0], -rhs[3]]);
    output[3] = dot_product_i64(lhs, [rhs[3], rhs[2], rhs[1], rhs[0]]);
}

#[inline(always)]
fn conv4_i64(lhs: [i64; 4], rhs: [i64; 4], output: &mut [i64; 4]) {
    let u_p = [lhs[0] + lhs[2], lhs[1] + lhs[3]];
    let u_m = [lhs[0] - lhs[2], lhs[1] - lhs[3]];
    let v_p = [rhs[0] + rhs[2], rhs[1] + rhs[3]];
    let v_m = [rhs[0] - rhs[2], rhs[1] - rhs[3]];

    output[0] = dot_product_i64(u_m, [v_m[0], -v_m[1]]);
    output[1] = dot_product_i64(u_m, [v_m[1], v_m[0]]);
    output[2] = dot_product_i64(u_p, v_p);
    output[3] = dot_product_i64(u_p, [v_p[1], v_p[0]]);

    output[0] += output[2];
    output[1] += output[3];
    output[0] >>= 1;
    output[1] >>= 1;
    output[2] -= output[0];
    output[3] -= output[1];
}

/// negacyclic_conv8 via even/odd decomposition with 3× negacyclic_conv4.
#[inline(always)]
fn negacyclic_conv8_i64(lhs: [i64; 8], rhs: [i64; 8], output: &mut [i64; 8]) {
    let mut lhs_even = [0i64; 4];
    let mut lhs_odd = [0i64; 4];
    let mut lhs_sum = [0i64; 4];
    let mut rhs_even = [0i64; 4];
    let mut rhs_odd = [0i64; 4];
    let mut rhs_sum = [0i64; 4];

    for i in 0..4 {
        lhs_even[i] = lhs[2 * i];
        lhs_odd[i] = lhs[2 * i + 1];
        lhs_sum[i] = lhs[2 * i] + lhs[2 * i + 1];

        rhs_even[i] = rhs[2 * i];
        rhs_odd[i] = rhs[2 * i + 1];
        rhs_sum[i] = rhs[2 * i] + rhs[2 * i + 1];
    }

    let mut even_conv = [0i64; 4];
    let mut odd_conv = [0i64; 4];
    let mut sum_conv = [0i64; 4];

    negacyclic_conv4_i64(lhs_even, rhs_even, &mut even_conv);
    negacyclic_conv4_i64(lhs_odd, rhs_odd, &mut odd_conv);
    negacyclic_conv4_i64(lhs_sum, rhs_sum, &mut sum_conv);

    // Karatsuba recombination
    sum_conv[0] -= even_conv[0] + odd_conv[0];
    even_conv[0] -= odd_conv[3]; // odd_conv[HALF_N - 1]

    for i in 1..4 {
        sum_conv[i] -= even_conv[i] + odd_conv[i];
        even_conv[i] += odd_conv[i - 1];
    }

    // Interleave: output[2i] = even_conv[i], output[2i+1] = sum_conv[i]
    for i in 0..4 {
        output[2 * i] = even_conv[i];
        output[2 * i + 1] = sum_conv[i];
    }
}

/// conv8 via CRT decomposition: negacyclic_conv4 + conv4.
#[inline(always)]
fn conv8_i64(lhs: [i64; 8], rhs: [i64; 8], output: &mut [i64; 8]) {
    let mut lhs_pos = [0i64; 4];
    let mut lhs_neg = [0i64; 4];
    let mut rhs_pos = [0i64; 4];
    let mut rhs_neg = [0i64; 4];

    for i in 0..4 {
        lhs_pos[i] = lhs[i] + lhs[i + 4];
        lhs_neg[i] = lhs[i] - lhs[i + 4];
        rhs_pos[i] = rhs[i] + rhs[i + 4];
        rhs_neg[i] = rhs[i] - rhs[i + 4];
    }

    let mut left = [0i64; 4];
    let mut right = [0i64; 4];

    negacyclic_conv4_i64(lhs_neg, rhs_neg, &mut left);
    conv4_i64(lhs_pos, rhs_pos, &mut right);

    for i in 0..4 {
        left[i] += right[i];
        left[i] >>= 1;
        right[i] -= left[i];
    }

    output[..4].copy_from_slice(&left);
    output[4..8].copy_from_slice(&right);
}

/// conv16 via CRT decomposition: negacyclic_conv8 + conv8.
#[inline(always)]
fn conv16_i64(lhs: [i64; 16], rhs: [i64; 16], output: &mut [i64; 16]) {
    let mut lhs_pos = [0i64; 8];
    let mut lhs_neg = [0i64; 8];
    let mut rhs_pos = [0i64; 8];
    let mut rhs_neg = [0i64; 8];

    for i in 0..8 {
        lhs_pos[i] = lhs[i] + lhs[i + 8];
        lhs_neg[i] = lhs[i] - lhs[i + 8];
        rhs_pos[i] = rhs[i] + rhs[i + 8];
        rhs_neg[i] = rhs[i] - rhs[i + 8];
    }

    let mut left = [0i64; 8];
    let mut right = [0i64; 8];

    negacyclic_conv8_i64(lhs_neg, rhs_neg, &mut left);
    conv8_i64(lhs_pos, rhs_pos, &mut right);

    for i in 0..8 {
        left[i] += right[i];
        left[i] >>= 1;
        right[i] -= left[i];
    }

    output[..8].copy_from_slice(&left);
    output[8..16].copy_from_slice(&right);
}

/// Apply the 16x16 circulant MDS matrix using Karatsuba convolution.
/// Specialized for KoalaBear: works in i64 with deferred modular reduction.
#[inline]
fn mds_circulant_16_karatsuba_i64(state: &mut [KoalaBear; 16]) {
    let lhs: [i64; 16] = std::array::from_fn(|i| state[i].value as i64);
    let mut output = [0i64; 16];
    conv16_i64(lhs, MDS_CIRC_16_FIRST_COL, &mut output);
    let p = KoalaBearParameters::PRIME as u64;
    for i in 0..16 {
        debug_assert!(output[i] >= 0);
        state[i] = KoalaBear::new_monty((output[i] as u64 % p) as u32);
    }
}

// ---------------------------------------------------------------------------
// Generic Karatsuba convolution for non-KoalaBear types (extension fields, packed fields, etc.)
// Same algorithmic structure as the i64 path, but over a generic PrimeCharacteristicRing.
// Division by 2 uses the modular inverse: (p+1)/2 where p = 2130706433 (KoalaBear prime).
// ---------------------------------------------------------------------------

/// (p+1)/2 for KoalaBear prime p = 2130706433. Multiplicative inverse of 2 in the field.
const KOALABEAR_TWO_INV: u64 = 1065353217;

#[inline(always)]
fn negacyclic_conv4_generic<R: PrimeCharacteristicRing>(lhs: &[R; 4], rhs: &[R; 4], output: &mut [R; 4]) {
    output[0] = lhs[0].clone() * rhs[0].clone()
        - lhs[1].clone() * rhs[3].clone()
        - lhs[2].clone() * rhs[2].clone()
        - lhs[3].clone() * rhs[1].clone();
    output[1] = lhs[0].clone() * rhs[1].clone() + lhs[1].clone() * rhs[0].clone()
        - lhs[2].clone() * rhs[3].clone()
        - lhs[3].clone() * rhs[2].clone();
    output[2] = lhs[0].clone() * rhs[2].clone() + lhs[1].clone() * rhs[1].clone() + lhs[2].clone() * rhs[0].clone()
        - lhs[3].clone() * rhs[3].clone();
    output[3] = lhs[0].clone() * rhs[3].clone()
        + lhs[1].clone() * rhs[2].clone()
        + lhs[2].clone() * rhs[1].clone()
        + lhs[3].clone() * rhs[0].clone();
}

#[inline(always)]
fn conv4_generic<R: PrimeCharacteristicRing>(lhs: &[R; 4], rhs: &[R; 4], output: &mut [R; 4]) {
    let two_inv = R::from_u64(KOALABEAR_TWO_INV);
    let u_p = [lhs[0].clone() + lhs[2].clone(), lhs[1].clone() + lhs[3].clone()];
    let u_m = [lhs[0].clone() - lhs[2].clone(), lhs[1].clone() - lhs[3].clone()];
    let v_p = [rhs[0].clone() + rhs[2].clone(), rhs[1].clone() + rhs[3].clone()];
    let v_m = [rhs[0].clone() - rhs[2].clone(), rhs[1].clone() - rhs[3].clone()];

    output[0] = u_m[0].clone() * v_m[0].clone() - u_m[1].clone() * v_m[1].clone();
    output[1] = u_m[0].clone() * v_m[1].clone() + u_m[1].clone() * v_m[0].clone();
    output[2] = u_p[0].clone() * v_p[0].clone() + u_p[1].clone() * v_p[1].clone();
    output[3] = u_p[0].clone() * v_p[1].clone() + u_p[1].clone() * v_p[0].clone();

    output[0] += output[2].clone();
    output[1] += output[3].clone();
    output[0] = output[0].clone() * two_inv.clone();
    output[1] = output[1].clone() * two_inv;
    output[2] -= output[0].clone();
    output[3] -= output[1].clone();
}

/// negacyclic_conv8 via even/odd decomposition with 3x negacyclic_conv4.
#[inline(always)]
fn negacyclic_conv8_generic<R: PrimeCharacteristicRing>(lhs: &[R; 8], rhs: &[R; 8], output: &mut [R; 8]) {
    let lhs_even: [R; 4] = std::array::from_fn(|i| lhs[2 * i].clone());
    let lhs_odd: [R; 4] = std::array::from_fn(|i| lhs[2 * i + 1].clone());
    let lhs_sum: [R; 4] = std::array::from_fn(|i| lhs[2 * i].clone() + lhs[2 * i + 1].clone());
    let rhs_even: [R; 4] = std::array::from_fn(|i| rhs[2 * i].clone());
    let rhs_odd: [R; 4] = std::array::from_fn(|i| rhs[2 * i + 1].clone());
    let rhs_sum: [R; 4] = std::array::from_fn(|i| rhs[2 * i].clone() + rhs[2 * i + 1].clone());

    let mut even_conv: [R; 4] = std::array::from_fn(|_| R::default());
    let mut odd_conv: [R; 4] = std::array::from_fn(|_| R::default());
    let mut sum_conv: [R; 4] = std::array::from_fn(|_| R::default());

    negacyclic_conv4_generic(&lhs_even, &rhs_even, &mut even_conv);
    negacyclic_conv4_generic(&lhs_odd, &rhs_odd, &mut odd_conv);
    negacyclic_conv4_generic(&lhs_sum, &rhs_sum, &mut sum_conv);

    // Karatsuba recombination
    sum_conv[0] -= even_conv[0].clone() + odd_conv[0].clone();
    even_conv[0] -= odd_conv[3].clone();
    for i in 1..4 {
        sum_conv[i] -= even_conv[i].clone() + odd_conv[i].clone();
        even_conv[i] += odd_conv[i - 1].clone();
    }

    // Interleave
    for i in 0..4 {
        output[2 * i] = even_conv[i].clone();
        output[2 * i + 1] = sum_conv[i].clone();
    }
}

/// conv8 via CRT decomposition: negacyclic_conv4 + conv4.
#[inline(always)]
fn conv8_generic<R: PrimeCharacteristicRing>(lhs: &[R; 8], rhs: &[R; 8], output: &mut [R; 8]) {
    let two_inv = R::from_u64(KOALABEAR_TWO_INV);
    let lhs_pos: [R; 4] = std::array::from_fn(|i| lhs[i].clone() + lhs[i + 4].clone());
    let lhs_neg: [R; 4] = std::array::from_fn(|i| lhs[i].clone() - lhs[i + 4].clone());
    let rhs_pos: [R; 4] = std::array::from_fn(|i| rhs[i].clone() + rhs[i + 4].clone());
    let rhs_neg: [R; 4] = std::array::from_fn(|i| rhs[i].clone() - rhs[i + 4].clone());

    let mut left: [R; 4] = std::array::from_fn(|_| R::default());
    let mut right: [R; 4] = std::array::from_fn(|_| R::default());

    negacyclic_conv4_generic(&lhs_neg, &rhs_neg, &mut left);
    conv4_generic(&lhs_pos, &rhs_pos, &mut right);

    for i in 0..4 {
        left[i] += right[i].clone();
        left[i] = left[i].clone() * two_inv.clone();
        right[i] -= left[i].clone();
    }

    output[..4].clone_from_slice(&left);
    output[4..8].clone_from_slice(&right);
}

/// conv16 via CRT decomposition: negacyclic_conv8 + conv8.
#[inline(always)]
fn conv16_generic<R: PrimeCharacteristicRing>(lhs: &[R; 16], rhs: &[R; 16], output: &mut [R; 16]) {
    let two_inv = R::from_u64(KOALABEAR_TWO_INV);
    let lhs_pos: [R; 8] = std::array::from_fn(|i| lhs[i].clone() + lhs[i + 8].clone());
    let lhs_neg: [R; 8] = std::array::from_fn(|i| lhs[i].clone() - lhs[i + 8].clone());
    let rhs_pos: [R; 8] = std::array::from_fn(|i| rhs[i].clone() + rhs[i + 8].clone());
    let rhs_neg: [R; 8] = std::array::from_fn(|i| rhs[i].clone() - rhs[i + 8].clone());

    let mut left: [R; 8] = std::array::from_fn(|_| R::default());
    let mut right: [R; 8] = std::array::from_fn(|_| R::default());

    negacyclic_conv8_generic(&lhs_neg, &rhs_neg, &mut left);
    conv8_generic(&lhs_pos, &rhs_pos, &mut right);

    for i in 0..8 {
        left[i] += right[i].clone();
        left[i] = left[i].clone() * two_inv.clone();
        right[i] -= left[i].clone();
    }

    output[..8].clone_from_slice(&left);
    output[8..16].clone_from_slice(&right);
}

/// Apply the 16x16 circulant MDS matrix to a state vector using Karatsuba convolution.
///
/// Uses i64 fast path for scalar KoalaBear (deferred modular reduction).
/// Uses generic Karatsuba convolution for all other types (extension fields, packed fields).
#[inline]
pub fn mds_circulant_16_karatsuba<R: PrimeCharacteristicRing + 'static>(state: &mut [R; 16]) {
    // Fast path for scalar KoalaBear: Karatsuba convolution in i64
    if TypeId::of::<R>() == TypeId::of::<KoalaBear>() {
        let state_kb = unsafe { &mut *(state as *mut [R; 16] as *mut [KoalaBear; 16]) };
        mds_circulant_16_karatsuba_i64(state_kb);
        return;
    }

    let lhs = state.clone();
    let rhs: [R; 16] = std::array::from_fn(|i| R::from_u64(MDS_CIRC_16_FIRST_COL[i] as u64));
    conv16_generic(&lhs, &rhs, state);
}

/// The Poseidon1 permutation for KoalaBear, width 16, cube S-box.
#[derive(Clone, Debug)]
pub struct Poseidon1KoalaBear16 {
    /// Round constants: 16 per round, for all 28 rounds.
    /// Layout: [initial_full_0, initial_full_1, ..., initial_full_3,
    ///          partial_0, partial_1, ..., partial_19,
    ///          final_full_0, final_full_1, ..., final_full_3]
    constants: Vec<[KoalaBear; 16]>,
}

impl Poseidon1KoalaBear16 {
    pub fn new(constants: Vec<[KoalaBear; 16]>) -> Self {
        let expected = 2 * POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS;
        assert_eq!(constants.len(), expected, "Expected {expected} rounds of constants");
        Self { constants }
    }

    /// Get constants for initial full rounds (first 4 rounds).
    #[inline]
    pub fn initial_constants(&self) -> &[[KoalaBear; 16]] {
        &self.constants[..POSEIDON1_HALF_FULL_ROUNDS]
    }

    /// Get constants for partial rounds (middle 20 rounds).
    #[inline]
    pub fn partial_constants(&self) -> &[[KoalaBear; 16]] {
        &self.constants[POSEIDON1_HALF_FULL_ROUNDS..POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS]
    }

    /// Get constants for final full rounds (last 4 rounds).
    #[inline]
    pub fn final_constants(&self) -> &[[KoalaBear; 16]] {
        &self.constants[POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS..]
    }

    /// Apply the permutation to a state, works generically on any Algebra<KoalaBear>.
    #[inline]
    fn permute_generic<R: Algebra<KoalaBear> + InjectiveMonomial<3> + 'static>(&self, state: &mut [R; 16]) {
        // Initial full rounds
        for rc in self.initial_constants() {
            Self::full_round(state, rc);
        }

        // Partial rounds
        for rc in self.partial_constants() {
            Self::partial_round(state, rc);
        }

        // Final full rounds
        for rc in self.final_constants() {
            Self::full_round(state, rc);
        }
    }

    /// A full round: add constants to all elements, cube all elements, apply MDS.
    #[inline(always)]
    fn full_round<R: Algebra<KoalaBear> + InjectiveMonomial<3> + 'static>(state: &mut [R; 16], rc: &[KoalaBear; 16]) {
        for (s, &c) in state.iter_mut().zip(rc.iter()) {
            *s += c;
            *s = s.injective_exp_n();
        }
        mds_circulant_16_karatsuba(state);
    }

    /// A partial round: add constants to all elements, cube only state[0], apply MDS.
    #[inline(always)]
    fn partial_round<R: Algebra<KoalaBear> + InjectiveMonomial<3> + 'static>(
        state: &mut [R; 16],
        rc: &[KoalaBear; 16],
    ) {
        for (s, &c) in state.iter_mut().zip(rc.iter()) {
            *s += c;
        }
        state[0] = state[0].injective_exp_n();
        mds_circulant_16_karatsuba(state);
    }

    /// Compression: output = perm(input) + input
    #[inline]
    pub fn compress_in_place<R: Algebra<KoalaBear> + InjectiveMonomial<3> + 'static>(&self, state: &mut [R; 16]) {
        let initial = state.clone();
        self.permute_generic(state);
        for (s, init) in state.iter_mut().zip(initial) {
            *s += init;
        }
    }
}

impl<R: Algebra<KoalaBear> + InjectiveMonomial<3> + Send + Sync + 'static> Permutation<[R; 16]>
    for Poseidon1KoalaBear16
{
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

/// Get constants for initial full rounds (first 4 rounds).
pub const fn get_poseidon1_initial_constants() -> &'static [[KoalaBear; 16]; POSEIDON1_HALF_FULL_ROUNDS] {
    let all: &[[KoalaBear; 16]] = &POSEIDON1_ROUND_CONSTANTS;
    let (initial, _) = all.split_first_chunk().unwrap();
    initial
}

/// Get constants for partial rounds (middle 20 rounds).
pub const fn get_poseidon1_partial_constants() -> &'static [[KoalaBear; 16]; POSEIDON1_PARTIAL_ROUNDS] {
    let all: &[[KoalaBear; 16]] = &POSEIDON1_ROUND_CONSTANTS;
    let (_, rest) = all.split_first_chunk::<POSEIDON1_HALF_FULL_ROUNDS>().unwrap();
    let (partial, _) = rest.split_first_chunk().unwrap();
    partial
}

/// Get constants for final full rounds (last 4 rounds).
pub const fn get_poseidon1_final_constants() -> &'static [[KoalaBear; 16]; POSEIDON1_HALF_FULL_ROUNDS] {
    let all: &[[KoalaBear; 16]] = &POSEIDON1_ROUND_CONSTANTS;
    all.last_chunk().unwrap()
}

/// Create a default Poseidon1 instance for KoalaBear width 16.
pub fn default_koalabear_poseidon1_16() -> Poseidon1KoalaBear16 {
    Poseidon1KoalaBear16::new(POSEIDON1_ROUND_CONSTANTS.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::KoalaBear;
    use field::PrimeField32;

    /// Regenerate and verify the POSEIDON1_ROUND_CONSTANTS array.
    /// Run with: cargo test -p mt-koala-bear -- generate_poseidon1_constants --ignored --nocapture
    #[test]
    fn generate_poseidon1_constants() {
        const P: u64 = 2130706433;
        const TOTAL: usize = POSEIDON1_N_ROUNDS * 16;

        let mut state: u64 = 0x506F736569646F6E; // "Poseidon" as seed
        let a: u64 = 6364136223846793005;
        let c: u64 = 1442695040888963407;

        let mut values = Vec::with_capacity(TOTAL);
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
            let vals: Vec<_> = chunk.iter().map(|v| v.as_canonical_u32().to_string()).collect();
            println!("    [{}],", vals.join(", "));
        }
        println!("]);");
    }

    /// Cross-check unrolled MDS against naive loop implementation.
    #[test]
    fn test_mds_circulant_matches_naive() {
        fn naive_mds(state: &mut [KoalaBear; 16]) {
            let input = *state;
            for i in 0..16 {
                let mut acc = KoalaBear::ZERO;
                for j in 0..16 {
                    let c = MDS_CIRC_16_FIRST_ROW[(j + 16 - i) % 16];
                    acc += KoalaBear::new(c as u32) * input[j];
                }
                state[i] = acc;
            }
        }

        for seed in 0u32..100 {
            let mut state_a: [KoalaBear; 16] = std::array::from_fn(|i| KoalaBear::new(seed * 16 + i as u32 + 1));
            let mut state_b = state_a;
            mds_circulant_16_karatsuba(&mut state_a);
            naive_mds(&mut state_b);
            assert_eq!(state_a, state_b, "Mismatch at seed={seed}");
        }
    }
}
