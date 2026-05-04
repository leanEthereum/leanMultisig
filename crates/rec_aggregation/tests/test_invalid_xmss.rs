use backend::*;
use lean_vm::F;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rec_aggregation::{init_aggregation_bytecode, xmss_aggregate};
use xmss::*;

/// Nonce found by `find_minus_one_limb_nonce` such that
/// `StdRng::seed_from_u64(NONCE).random()` produces a randomness whose
/// `encoding_fe` digest contains a `-F::ONE = p - 1` limb (triggering the
/// `assert remaining_i < 127` check in `xmss_aggregate.py`). Re-run the
/// `#[ignore]` test below if any of the involved hashes / inputs change.
const MINUS_ONE_LIMB_NONCE: u64 = 9223372036864811589;

fn assert_aggregate_rejects(
    find_bad_randomness: impl FnOnce(&XmssPublicKey, &[F; MESSAGE_LEN_FE], u32) -> [F; RANDOMNESS_LEN_FE],
) {
    init_aggregation_bytecode();
    let seed: [u8; 32] = std::array::from_fn(|i| (i.wrapping_mul(13).wrapping_add(7)) as u8);
    let slot = 0;
    let (sk, pk) = xmss_key_gen(seed, slot, slot).unwrap();
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i + 1));
    let sig = xmss_sign(&mut StdRng::seed_from_u64(0), &sk, &message, slot).unwrap();

    let randomness = find_bad_randomness(&pk, &message, slot);
    let bad_sig = XmssSignature {
        wots_signature: WotsSignature {
            chain_tips: sig.wots_signature.chain_tips,
            randomness,
        },
        merkle_proof: sig.merkle_proof,
    };
    assert!(
        xmss_aggregate(&[], vec![(pk, bad_sig)], &message, slot, 1).is_err(),
        "expected aggregation to fail"
    );
}

/// `wots_encode` returns `None` (uniformity / gap-zero / target-sum check fails).
#[test]
fn aggregate_rejects_invalid_encoding() {
    assert_aggregate_rejects(|pk, message, slot| {
        let mut rng = StdRng::seed_from_u64(1);
        loop {
            let r = rng.random();
            if wots_encode(message, slot, pk, &r).is_none() {
                return r;
            }
        }
    });
}

/// should fail because of `assert remaining_i < 127` in xmss_aggregate.py
#[test]
fn aggregate_rejects_minus_one_limb() {
    assert_aggregate_rejects(|_pk, _message, _slot| StdRng::seed_from_u64(MINUS_ONE_LIMB_NONCE).random());
}

/// Searches for a nonce whose seeded randomness produces a `-F::ONE` limb
/// (~1 in 2^28 digests, so the search takes ~minutes).
/// `cargo test --release -p rec_aggregation --test test_invalid_xmss find_minus_one_limb_nonce -- --ignored --nocapture`
#[test]
#[ignore = "expensive parallel search (~minutes)"]
fn find_minus_one_limb_nonce() {
    let seed: [u8; 32] = std::array::from_fn(|i| (i.wrapping_mul(13).wrapping_add(7)) as u8);
    let slot: u32 = 0;
    let (_sk, pk) = xmss_key_gen(seed, slot, slot).unwrap();
    let message: [F; MESSAGE_LEN_FE] = std::array::from_fn(|i| F::from_usize(i + 1));

    let nonce = (0u64..u64::MAX)
        .into_par_iter()
        .find_any(|&nonce| {
            let r: [F; RANDOMNESS_LEN_FE] = StdRng::seed_from_u64(nonce).random();
            wots_encode_fe(&message, slot, &pk, &r).iter().any(|&kb| kb == -F::ONE)
        })
        .expect("not found");
    println!("found nonce = {nonce}");
}
