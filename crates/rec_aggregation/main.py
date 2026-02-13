from recursion import *
from xmss_aggregate import *

MAX_RECURSIONS = 16
LOG_SIZE_PUBKEY_REGISTRY = LOG_SIZE_PUBKEY_REGISTRY_PLACEHOLDER
DATA_PER_RAW_SIGNER = DIGEST_LEN + LOG_SIZE_PUBKEY_REGISTRY * DIGEST_LEN + SIG_SIZE
INNER_PUB_MEM_SIZE = 2 ** INNER_PUBLIC_MEMORY_LOG_SIZE
BYTECODE_CLAIM_OFFSET = 2 + 2 * DIGEST_LEN + 2 + MESSAGE_LEN + N_MERKLE_CHUNKS


def main():
    pub_mem = NONRESERVED_PROGRAM_INPUT_START
    n_sigs = pub_mem[0]
    assert n_sigs <= 2**LOG_SIZE_PUBKEY_REGISTRY
    n_recursions = pub_mem[1]
    assert n_recursions <= MAX_RECURSIONS
    registry_root = pub_mem + 2
    signer_indexes_hash_expected = registry_root + DIGEST_LEN
    message = signer_indexes_hash_expected + DIGEST_LEN
    slot_ptr = message + MESSAGE_LEN
    slot_lo = slot_ptr[0]
    slot_hi = slot_ptr[1]
    merkle_chunks_for_slot = slot_ptr + 2
    bytecode_claim_output = pub_mem + BYTECODE_CLAIM_OFFSET

    priv_start: Imu
    hint_private_input_start(priv_start)

    signer_indexes_hash, sub_slice_starts, bytecode_sumcheck_proof, source_hashes = verify_signer_index_partitioning(n_sigs, n_recursions, priv_start)

    copy_8(signer_indexes_hash, signer_indexes_hash_expected)

    verify_raw_xmss(sub_slice_starts[0], registry_root, message, slot_lo, slot_hi, merkle_chunks_for_slot)

    verify_recursive_sources_and_reduce_bytecode_claims(
        n_recursions, sub_slice_starts, source_hashes, bytecode_sumcheck_proof,
        registry_root, message, slot_lo, slot_hi, merkle_chunks_for_slot,
        bytecode_claim_output)
    return


def verify_signer_index_partitioning(n_sigs, n_recursions, priv_mem):
    sub_slice_starts = priv_mem
    bytecode_sumcheck_proof = priv_mem[n_recursions + 1]
    n_duplicates = priv_mem[n_recursions + 2]
    assert n_duplicates < 2**16 # TODO should we tolerate even more duplicates?
    global_indices = priv_mem + n_recursions + 3
    duplicate_indices = global_indices + n_sigs

    # Hash global indices
    global_hash = slice_hash_dynamic_unroll(global_indices, n_sigs, LOG_SIZE_PUBKEY_REGISTRY)

    # Hash duplicate indices
    duplicate_hash: Imu
    if n_duplicates == 0:
        duplicate_hash = ZERO_VEC_PTR
    else:
        duplicate_hash = slice_hash_dynamic_unroll(duplicate_indices, n_duplicates, LOG_SIZE_PUBKEY_REGISTRY)

    # Combine hashes: global, duplicate, and sub-indices, everything hashed together (for Fiat-Shamir challenge derivation)
    combined_hash: Mut = Array(DIGEST_LEN)
    poseidon16(global_hash, duplicate_hash, combined_hash)

    source_hashes = Array(n_recursions + 1)
    for s in range(0, n_recursions + 1):
        source_data = sub_slice_starts[s]
        n_sub = source_data[0]
        sub_indices_s = source_data + 1
        source_hash: Imu
        if n_sub == 0:
            source_hash = ZERO_VEC_PTR
        else:
            source_hash = slice_hash_dynamic_unroll(sub_indices_s, n_sub, LOG_SIZE_PUBKEY_REGISTRY)
        source_hashes[s] = source_hash
        new_combined = Array(DIGEST_LEN)
        poseidon16(combined_hash, source_hash, new_combined)
        combined_hash = new_combined

    # Derive challenge alpha from combined hash
    alpha = combined_hash

    # Polynomial identity check: P_global(alpha) * P_duplicate(alpha) == prod_s P_s(alpha)
    p_global = compute_product_polynomial(alpha, global_indices, n_sigs)
    p_dup = compute_product_polynomial(alpha, duplicate_indices, n_duplicates)
    lhs = mul_extension_ret(p_global, p_dup)

    rhs: Mut = Array(DIM)
    set_to_one(rhs)
    for s in range(0, n_recursions + 1):
        source_data = sub_slice_starts[s]
        n_sub = source_data[0]
        sub_indices_s = source_data + 1
        p_s = compute_product_polynomial(alpha, sub_indices_s, n_sub)
        rhs = mul_extension_ret(rhs, p_s)

    copy_5(lhs, rhs)

    return global_hash, sub_slice_starts, bytecode_sumcheck_proof, source_hashes


def compute_product_polynomial(alpha, indices, n):
    result: Mut = Array(DIM)
    alpha_0 = alpha[0]
    alpha_tail = alpha + 1
    set_to_one(result)
    for i in dynamic_unroll(0, n, LOG_SIZE_PUBKEY_REGISTRY):
        factor = Array(DIM + 1)
        factor[0] = alpha_0 - indices[i]
        copy_5(alpha_tail, factor + 1)
        result = mul_extension_ret(result, factor)
    return result


def verify_raw_xmss(data_block, registry_root, message, slot_lo, slot_hi, merkle_chunks_for_slot):
    n_raw_xmss = data_block[0]
    raw_indices = data_block + 1
    raw_data = raw_indices + n_raw_xmss

    for i in range(0, n_raw_xmss):
        signer_index = raw_indices[i]
        signer_data = raw_data + i * DATA_PER_RAW_SIGNER
        pubkey = signer_data
        registry_proof = signer_data + DIGEST_LEN
        xmss_sig = signer_data + DIGEST_LEN + LOG_SIZE_PUBKEY_REGISTRY * DIGEST_LEN

        # Decompose signer_index to bits for registry merkle proof
        signer_index_bits = checked_decompose_bits_small_value(signer_index, LOG_SIZE_PUBKEY_REGISTRY)

        # Verify pubkey is in registry merkle tree
        merkle_verify(pubkey, registry_proof, signer_index_bits, registry_root, LOG_SIZE_PUBKEY_REGISTRY)

        # Verify XMSS signature
        xmss_verify(pubkey, message, xmss_sig, slot_lo, slot_hi, merkle_chunks_for_slot)
    return


def verify_recursive_sources_and_reduce_bytecode_claims(
    n_recursions, sub_slice_starts, source_hashes, bytecode_sumcheck_proof,
    registry_root, message, slot_lo, slot_hi, merkle_chunks_for_slot,
    bytecode_claim_output):

    if n_recursions == 0:
        for k in unroll(0, BYTECODE_POINT_N_VARS):
            set_to_5_zeros(bytecode_claim_output + k * DIM)
        bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM] = BYTECODE_ZERO_EVAL
        for k in unroll(1, DIM):
            bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM + k] = 0
        return

    n_bytecode_claims = n_recursions * 2
    bytecode_claims = Array(n_bytecode_claims)

    for rec_idx in range(0, n_recursions):
        source_data = sub_slice_starts[rec_idx + 1]
        n_sub_sigs = source_data[0]
        sub_indices = source_data + 1
        bytecode_value_hint = sub_indices + n_sub_sigs # hinted evaluation of bytecode, used to verify the recursive proof, and verified at the end (2n->1 sumcheck reduction)
        inner_pub_mem = bytecode_value_hint + DIM
        proof_transcript = inner_pub_mem + INNER_PUB_MEM_SIZE

        sub_indexes_hash = source_hashes[rec_idx + 1]

        # Verify inner public memory matches expected structure
        debug_assert(NONRESERVED_PROGRAM_INPUT_START % DIM == 0) # NONRESERVED_PROGRAM_INPUT_START should be a multiple of DIM
        for i in unroll(0, NONRESERVED_PROGRAM_INPUT_START / DIM):
            copy_5(i * DIM, inner_pub_mem + i * DIM)
        non_reserserved_inner_pub_mem = inner_pub_mem + NONRESERVED_PROGRAM_INPUT_START
        assert non_reserserved_inner_pub_mem[0] == n_sub_sigs
        copy_8(registry_root, non_reserserved_inner_pub_mem + 2)
        copy_8(sub_indexes_hash, non_reserserved_inner_pub_mem + 2 + DIGEST_LEN)
        inner_msg = non_reserserved_inner_pub_mem + 2 + 2 * DIGEST_LEN
        debug_assert(MESSAGE_LEN <= 2*DIM)
        copy_5(message, inner_msg)
        copy_5(message + (MESSAGE_LEN - DIM), inner_msg + (MESSAGE_LEN - DIM) )
        inner_msg[MESSAGE_LEN] = slot_lo
        inner_msg[MESSAGE_LEN + 1] = slot_hi
        for k in unroll(0, N_MERKLE_CHUNKS):
            inner_msg[MESSAGE_LEN + 2 + k] = merkle_chunks_for_slot[k]

        # Collect inner bytecode claim from inner pub mem
        bytecode_claims[2 * rec_idx] = non_reserserved_inner_pub_mem + BYTECODE_CLAIM_OFFSET

        # Verify recursive proof - returns the second bytecode claim
        bytecode_claims[2 * rec_idx + 1] = recursion(inner_pub_mem, proof_transcript, bytecode_value_hint)

    # Bytecode claims reduction: 2n -> 1 via sumcheck
    bytecode_claims_hash: Mut = ZERO_VEC_PTR
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
            assert claim_ptr[k] == 0
        claim_hash = slice_hash(claim_ptr, BYTECODE_CLAIM_SIZE_PADDED / DIGEST_LEN)
        new_hash = Array(DIGEST_LEN)
        poseidon16(bytecode_claims_hash, claim_hash, new_hash)
        bytecode_claims_hash = new_hash

    reduction_fs: Mut = fs_new(bytecode_sumcheck_proof)
    reduction_fs, received_claims_hash = fs_receive_chunks(reduction_fs, 1)
    copy_8(bytecode_claims_hash, received_claims_hash)

    reduction_fs, alpha = fs_sample_ef(reduction_fs)
    alpha_powers = powers(alpha, n_bytecode_claims)

    all_values = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        copy_5(claim_ptr + BYTECODE_POINT_N_VARS * DIM, all_values + i * DIM)

    claimed_sum = Array(DIM)
    dot_product_ee_dynamic(all_values, alpha_powers, claimed_sum, n_bytecode_claims)

    reduction_fs, challenges, final_eval = sumcheck_verify(reduction_fs, BYTECODE_POINT_N_VARS, claimed_sum, 2)

    # Verify: final_eval == bytecode(r) * w(r)
    eq_evals = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        eq_val = eq_mle_extension(claim_ptr, challenges, BYTECODE_POINT_N_VARS)
        copy_5(eq_val, eq_evals + i * DIM)
    w_r = Array(DIM)
    dot_product_ee_dynamic(eq_evals, alpha_powers, w_r, n_bytecode_claims)

    bytecode_value_at_r = div_extension_ret(final_eval, w_r)

    copy_many_ef(challenges, bytecode_claim_output, BYTECODE_POINT_N_VARS)
    copy_5(bytecode_value_at_r, bytecode_claim_output + BYTECODE_POINT_N_VARS * DIM)
    return
