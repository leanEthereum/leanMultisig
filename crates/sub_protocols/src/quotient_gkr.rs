use backend::*;

use crate::N_VARS_TO_SEND_GKR_COEFFS;

/*
GKR to compute a sum of fractions, right-to-left variant.

Conventions (same as crates/sub_protocols/src/air_sumcheck.rs):
  - MLE storage is lexicographic: for a MultilinearPoint (x_0, ..., x_{L-1}),
    x_0 is the MSB of the storage index and x_{L-1} is the LSB.
  - Variables are bound right-to-left: round 0 binds X_{K-1} (the LSB of the
    storage), round r binds X_{K-1-r}. Accordingly the GKR layer reduction
    collapses the LSB (pairs (2i, 2i+1)), and the per-layer sumcheck also
    folds the LSB first.
  - This implementation is intentionally unoptimized: everything runs on
    Vec<EF>. No packing, no bit reversal, no SplitEq. Those come back later.
*/

pub fn prove_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    numerators: &MleRef<'_, EF>,
    denominators: &MleRef<'_, EF>,
) -> (EF, MultilinearPoint<EF>, EF, EF) {
    assert_eq!(numerators.n_vars(), denominators.n_vars());
    assert!(numerators.n_vars() > N_VARS_TO_SEND_GKR_COEFFS);

    let nums0: Vec<EF> = mle_ref_to_vec_ef(numerators);
    let dens0: Vec<EF> = mle_ref_to_vec_ef(denominators);

    let mut layers: Vec<(Vec<EF>, Vec<EF>)> = vec![(nums0, dens0)];
    loop {
        let (cur_n, cur_d) = layers.last().unwrap();
        let n_vars = cur_n.len().trailing_zeros() as usize;
        if n_vars <= N_VARS_TO_SEND_GKR_COEFFS {
            break;
        }
        let (nn, nd) = sum_quotients(cur_n, cur_d);
        layers.push((nn, nd));
    }

    let (top_nums, top_dens) = layers.pop().unwrap();
    prover_state.add_extension_scalars(&top_nums);
    prover_state.add_extension_scalars(&top_dens);
    let quotient = compute_quotient(&top_nums, &top_dens);

    let mut point = MultilinearPoint(prover_state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS));
    let mut claim_num = top_nums.evaluate(&point);
    let mut claim_den = top_dens.evaluate(&point);

    for (nums, dens) in layers.iter().rev() {
        let (next_point, next_num, next_den) =
            prove_gkr_quotient_step(prover_state, nums, dens, &point, claim_num, claim_den);
        point = next_point;
        claim_num = next_num;
        claim_den = next_den;
    }

    (quotient, point, claim_num, claim_den)
}

fn prove_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    nums: &[EF], // layer of size 2^{K+1}
    dens: &[EF],
    claim_point: &MultilinearPoint<EF>, // K coords, natural order
    claim_num: EF,
    claim_den: EF,
) -> (MultilinearPoint<EF>, EF, EF) {
    let alpha = prover_state.sample();
    let expected_sum = claim_num + alpha * claim_den;

    // LSB split of the parent layer.
    let (num_l, num_r) = even_odd_split(nums);
    let (den_l, den_r) = even_odd_split(dens);

    let (mut q_natural, inner_evals) = rtl_gkr_quotient_sumcheck_prove(
        prover_state,
        num_l,
        num_r,
        den_l,
        den_r,
        &claim_point.0,
        alpha,
        expected_sum,
    );

    prover_state.add_extension_scalars(&inner_evals);
    let beta = prover_state.sample();

    let nl_q = inner_evals[0];
    let nr_q = inner_evals[1];
    let dl_q = inner_evals[2];
    let dr_q = inner_evals[3];

    let one_minus_beta = EF::ONE - beta;
    let next_num = one_minus_beta * nl_q + beta * nr_q;
    let next_den = one_minus_beta * dl_q + beta * dr_q;

    // q_natural has K coords; new layer's claim point is q || [β] (β is the
    // new LSB, i.e. the X_K that was just reduced from the parent layer).
    q_natural.push(beta);
    (MultilinearPoint(q_natural), next_num, next_den)
}

// Runs a right-to-left sumcheck proving:
//   expected_sum = Σ_{b ∈ {0,1}^K} eq(b, eq_point)
//                   · [num_l(b)·den_r(b) + num_r(b)·den_l(b) + α · den_l(b)·den_r(b)]
//
// Each of `num_l, num_r, den_l, den_r` is a K-variable MLE stored in
// lexicographic order (its LSB = X_{K-1}).  We bind the LSB in round 0, the
// new LSB in round 1, and so on, until K challenges have been sampled.
//
// Returns (q, [num_l(q), num_r(q), den_l(q), den_r(q)]) where `q` is in
// natural order (x_0, ..., x_{K-1}).
#[allow(clippy::too_many_arguments)]
fn rtl_gkr_quotient_sumcheck_prove<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    mut num_l: Vec<EF>,
    mut num_r: Vec<EF>,
    mut den_l: Vec<EF>,
    mut den_r: Vec<EF>,
    eq_point: &[EF],
    alpha: EF,
    expected_sum: EF,
) -> (Vec<EF>, [EF; 4]) {
    let k = eq_point.len();
    debug_assert_eq!(num_l.len(), 1 << k);
    debug_assert_eq!(num_r.len(), 1 << k);
    debug_assert_eq!(den_l.len(), 1 << k);
    debug_assert_eq!(den_r.len(), 1 << k);

    // Invariant entering round r:
    //   sum = mmf · natural_H_r(evaluated via folded arrays)
    //   mmf = Π_{i<r} eq(α_i, r_i)
    // The round polynomial we send is mmf · natural_H_r(z); scaling by mmf keeps
    // the identity sum = (1-α_r)·h_r(0) + α_r·h_r(1) consistent with the
    // verifier's interpretation of the `Some(α)` back-loaded batching (which
    // tracks target *= eq(α_r, r_r) each round).
    let mut sum = expected_sum;
    let mut mmf = EF::ONE;
    // q is built in natural order: the first challenge we sample binds X_{K-1}
    // and so occupies slot K-1 of q; the next binds X_{K-2}, etc.  We prepend
    // each new challenge.
    let mut q_natural: Vec<EF> = Vec::with_capacity(k);

    // `remaining_eq` shrinks from the back each round — its last entry is the
    // eq factor associated with the variable currently being bound.
    let mut remaining_eq: Vec<EF> = eq_point.to_vec();

    for _round in 0..k {
        let eq_alpha = *remaining_eq.last().unwrap();
        let eq_prefix: &[EF] = &remaining_eq[..remaining_eq.len() - 1];
        let eq_table: Vec<EF> = if eq_prefix.is_empty() {
            vec![EF::ONE]
        } else {
            eval_eq(eq_prefix)
        };

        let half = num_l.len() / 2; // number of LSB pairs
        debug_assert_eq!(eq_table.len(), half);

        // H(z) = Σ_j eq_table[j] · [ NL(j,z) · DR(j,z) + NR(j,z) · DL(j,z)
        //                           + α · DL(j,z) · DR(j,z) ]
        // where NL(j,z) = num_l[2j] + z·(num_l[2j+1] - num_l[2j]), etc.
        // H has degree 2; evaluate at z=0 and z=2, reconstruct z=1 from sum
        // constraint.
        let mut h0_raw = EF::ZERO;
        let mut h2_raw = EF::ZERO;
        for j in 0..half {
            let nl0 = num_l[2 * j];
            let nl1 = num_l[2 * j + 1];
            let nr0 = num_r[2 * j];
            let nr1 = num_r[2 * j + 1];
            let dl0 = den_l[2 * j];
            let dl1 = den_l[2 * j + 1];
            let dr0 = den_r[2 * j];
            let dr1 = den_r[2 * j + 1];

            let inner0 = nl0 * dr0 + nr0 * dl0 + alpha * dl0 * dr0;

            let nl2 = nl1.double() - nl0;
            let nr2 = nr1.double() - nr0;
            let dl2 = dl1.double() - dl0;
            let dr2 = dr1.double() - dr0;
            let inner2 = nl2 * dr2 + nr2 * dl2 + alpha * dl2 * dr2;

            h0_raw += eq_table[j] * inner0;
            h2_raw += eq_table[j] * inner2;
        }

        let h0 = h0_raw * mmf;
        let h2 = h2_raw * mmf;

        // sum = (1 - eq_alpha)·h(0) + eq_alpha·h(1)
        let h1 = (sum - (EF::ONE - eq_alpha) * h0) / eq_alpha;

        let bare = DensePolynomial::lagrange_interpolation(&[
            (PF::<EF>::ZERO, h0),
            (PF::<EF>::ONE, h1),
            (PF::<EF>::from_usize(2), h2),
        ])
        .unwrap();

        prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
        let r = prover_state.sample();

        // Next round's sum = full(r) = eq(eq_alpha, r) · h(r).
        let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
        sum = eq_eval * bare.evaluate(r);
        mmf *= eq_eval;

        num_l = fold_lsb(&num_l, r);
        num_r = fold_lsb(&num_r, r);
        den_l = fold_lsb(&den_l, r);
        den_r = fold_lsb(&den_r, r);

        q_natural.insert(0, r);
        remaining_eq.pop();
    }

    debug_assert_eq!(num_l.len(), 1);
    let evals = [num_l[0], num_r[0], den_l[0], den_r[0]];
    (q_natural, evals)
}

pub fn verify_gkr_quotient<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    n_vars: usize,
) -> Result<(EF, MultilinearPoint<EF>, EF, EF), ProofError> {
    assert!(n_vars > N_VARS_TO_SEND_GKR_COEFFS);
    let send_len = 1 << N_VARS_TO_SEND_GKR_COEFFS;
    let top_nums = verifier_state.next_extension_scalars_vec(send_len)?;
    let top_dens = verifier_state.next_extension_scalars_vec(send_len)?;
    let quotient = compute_quotient(&top_nums, &top_dens);

    let mut point = MultilinearPoint(verifier_state.sample_vec(N_VARS_TO_SEND_GKR_COEFFS));
    let mut claim_num = top_nums.evaluate(&point);
    let mut claim_den = top_dens.evaluate(&point);

    for k in N_VARS_TO_SEND_GKR_COEFFS..n_vars {
        let (next_point, next_num, next_den) =
            verify_gkr_quotient_step(verifier_state, k, &point, claim_num, claim_den)?;
        point = next_point;
        claim_num = next_num;
        claim_den = next_den;
    }

    Ok((quotient, point, claim_num, claim_den))
}

fn verify_gkr_quotient_step<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    k: usize,
    claim_point: &MultilinearPoint<EF>,
    claim_num: EF,
    claim_den: EF,
) -> Result<(MultilinearPoint<EF>, EF, EF), ProofError> {
    let alpha = verifier_state.sample();
    let expected_sum = claim_num + alpha * claim_den;

    let (q_natural, final_target) = rtl_gkr_quotient_sumcheck_verify(verifier_state, k, &claim_point.0, expected_sum)?;

    let inner_evals = verifier_state.next_extension_scalars_vec(4)?;
    let nl_q = inner_evals[0];
    let nr_q = inner_evals[1];
    let dl_q = inner_evals[2];
    let dr_q = inner_evals[3];

    let q_point = MultilinearPoint(q_natural.clone());
    let eq_factor = claim_point.eq_poly_outside(&q_point);
    let expected = eq_factor * (nl_q * dr_q + nr_q * dl_q + alpha * dl_q * dr_q);
    if final_target != expected {
        return Err(ProofError::InvalidProof);
    }

    let beta = verifier_state.sample();
    let one_minus_beta = EF::ONE - beta;
    let next_num = one_minus_beta * nl_q + beta * nr_q;
    let next_den = one_minus_beta * dl_q + beta * dr_q;

    let mut next_point = q_natural;
    next_point.push(beta);
    Ok((MultilinearPoint(next_point), next_num, next_den))
}

// Mirror of rtl_gkr_quotient_sumcheck_prove: walks eq_point from the back, one
// eq_alpha per round. Returns (q_natural, final_running_target) — the target
// the caller must then cross-check against the inner_evals.
fn rtl_gkr_quotient_sumcheck_verify<EF: ExtensionField<PF<EF>>>(
    verifier_state: &mut impl FSVerifier<EF>,
    k: usize,
    eq_point: &[EF],
    initial_sum: EF,
) -> Result<(Vec<EF>, EF), ProofError> {
    debug_assert_eq!(eq_point.len(), k);
    let mut target = initial_sum;
    let mut q_natural: Vec<EF> = Vec::with_capacity(k);
    for round in 0..k {
        let eq_alpha = eq_point[k - 1 - round];
        let coeffs = verifier_state.next_sumcheck_polynomial(4, target, Some(eq_alpha))?;
        let pol = DensePolynomial::new(coeffs);
        let r = verifier_state.sample();
        target = pol.evaluate(r);
        q_natural.insert(0, r);
    }
    Ok((q_natural, target))
}

fn sum_quotients<EF: ExtensionField<PF<EF>>>(nums: &[EF], dens: &[EF]) -> (Vec<EF>, Vec<EF>) {
    let n = nums.len();
    assert_eq!(n, dens.len());
    let new_n = n / 2;
    let mut new_nums = unsafe { uninitialized_vec(new_n) };
    let mut new_dens = unsafe { uninitialized_vec(new_n) };
    new_nums
        .par_iter_mut()
        .zip(new_dens.par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            // LSB pairing: combine storage positions 2i and 2i+1.
            let n0 = nums[2 * i];
            let n1 = nums[2 * i + 1];
            let d0 = dens[2 * i];
            let d1 = dens[2 * i + 1];
            *num = d1 * n0 + d0 * n1;
            *den = d0 * d1;
        });
    (new_nums, new_dens)
}

fn compute_quotient<EF: ExtensionField<PF<EF>>>(numerators: &[EF], denominators: &[EF]) -> EF {
    numerators.iter().zip(denominators).map(|(&n, &d)| n / d).sum()
}

fn mle_ref_to_vec_ef<EF: ExtensionField<PF<EF>>>(mle: &MleRef<'_, EF>) -> Vec<EF> {
    match mle {
        MleRef::Base(v) => v.iter().map(|&x| EF::from(x)).collect(),
        MleRef::Extension(v) => v.to_vec(),
        MleRef::BasePacked(pb) => PFPacking::<EF>::unpack_slice(pb).iter().map(|&x| EF::from(x)).collect(),
        MleRef::ExtensionPacked(ep) => unpack_extension(ep),
    }
}

fn even_odd_split<EF: Copy>(v: &[EF]) -> (Vec<EF>, Vec<EF>) {
    let half = v.len() / 2;
    let mut l = Vec::with_capacity(half);
    let mut r = Vec::with_capacity(half);
    for i in 0..half {
        l.push(v[2 * i]);
        r.push(v[2 * i + 1]);
    }
    (l, r)
}

fn fold_lsb<EF: ExtensionField<PF<EF>>>(u: &[EF], r: EF) -> Vec<EF> {
    (0..u.len() / 2)
        .map(|j| u[2 * j] + r * (u[2 * j + 1] - u[2 * j]))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{RngExt, SeedableRng, rngs::StdRng};
    use std::time::Instant;
    use utils::{build_prover_state, build_verifier_state, init_tracing};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    fn sum_all_quotients(nums: &[F], den: &[EF]) -> EF {
        nums.par_iter().zip(den).map(|(&n, &d)| EF::from(n) / d).sum()
    }

    #[test]
    fn test_gkr_quotient() {
        let log_n = 13;
        let n = 1 << log_n;
        init_tracing();

        let mut rng = StdRng::seed_from_u64(0);
        let numerators = (0..n).map(|_| rng.random()).collect::<Vec<F>>();
        let c: EF = rng.random();
        let denominators_indexes = (0..n)
            .map(|_| PF::<EF>::from_usize(rng.random_range(..n)))
            .collect::<Vec<_>>();
        let denominators = denominators_indexes.iter().map(|&i| c - i).collect::<Vec<EF>>();
        let real_quotient = sum_all_quotients(&numerators, &denominators);
        let mut prover_state = build_prover_state();

        let numerators = MleOwned::BasePacked(pack_extension(&numerators));
        let denominators = MleOwned::ExtensionPacked(pack_extension(&denominators));

        let time = Instant::now();
        let prover_statements =
            prove_gkr_quotient::<EF>(&mut prover_state, &numerators.by_ref(), &denominators.by_ref());
        println!("Proving time: {:?}", time.elapsed());

        let mut verifier_state = build_verifier_state(prover_state).unwrap();
        let verifier_statements = verify_gkr_quotient::<EF>(&mut verifier_state, log_n).unwrap();
        assert_eq!(&verifier_statements, &prover_statements);
        let (retrieved_quotient, claim_point, claim_num, claim_den) = verifier_statements;
        assert_eq!(retrieved_quotient, real_quotient);
        assert_eq!(numerators.evaluate(&claim_point), claim_num);
        assert_eq!(denominators.evaluate(&claim_point), claim_den);
    }
}
