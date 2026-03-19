from recursion import *
from xmss_aggregate import *

MAX_RECURSIONS = 16

# TODO increase (we would need a bigger minimal memory size, totally doable)
MAX_N_SIGS = 2**15
MAX_N_DUPS = 2**15

INNER_PUB_MEM_SIZE = 2**INNER_PUBLIC_MEMORY_LOG_SIZE
BYTECODE_CLAIM_OFFSET = 1 + DIGEST_LEN + 2 + MESSAGE_LEN + N_MERKLE_CHUNKS + N_ALL_TWEAKS


def main():
    debug_assert(MAX_N_SIGS + MAX_N_DUPS <= 2**16)  # because of range checking, TODO increase
    pub_mem = NONRESERVED_PROGRAM_INPUT_START
    n_sigs = pub_mem[0]
    assert n_sigs != 0
    assert n_sigs - 1 < MAX_N_SIGS
    pubkeys_hash_expected = pub_mem + 1
    message = pubkeys_hash_expected + DIGEST_LEN
    slot_ptr = message + MESSAGE_LEN
    slot_lo = slot_ptr[0]
    slot_hi = slot_ptr[1]
    merkle_chunks_for_slot = slot_ptr + 2
    all_tweaks = merkle_chunks_for_slot + N_MERKLE_CHUNKS
    bytecode_claim_output = pub_mem + BYTECODE_CLAIM_OFFSET

    priv_start: Imu
    hint_private_input_start(priv_start)

    n_recursions = priv_start[0]
    assert n_recursions <= MAX_RECURSIONS

    n_dup = priv_start[1]
    assert n_dup < MAX_N_SIGS  # TODO increase
    all_pubkeys = priv_start[2]
    sub_slice_starts = priv_start + 3
    bytecode_sumcheck_proof = sub_slice_starts[n_recursions + 1]

    source_0 = sub_slice_starts[0]
    n_raw_xmss = source_0[0]

    inv_mds_16: Imu
    inv_mds_24: Imu
    if n_recursions == 0:
        inv_mds_16 = 0
        inv_mds_24 = 0
    else:
        inv_mds_16 = Array(16**2)
        for i in unroll(0, 16**2):
            inv_mds_16[i] = INV_MDS_16[i]
        inv_mds_24 = Array(24**2)
        for i in unroll(0, 24**2):
            inv_mds_24[i] = INV_MDS_24[i]

    # 1->1 optimization
    if n_recursions == 1:
        assert n_dup == 0
        if n_raw_xmss == 0:
            source_data = sub_slice_starts[1]
            n_sub = source_data[0]
            assert n_sub != 0
            assert n_sub == n_sigs
            bytecode_value_hint = source_data + 1 + n_sub
            inner_pub_mem = bytecode_value_hint + DIM
            proof_transcript = inner_pub_mem + INNER_PUB_MEM_SIZE
            non_reserved_inner = verify_inner_pub_mem(inner_pub_mem, n_sigs, message, slot_lo, slot_hi, merkle_chunks_for_slot, all_tweaks, pub_mem)
            copy_8(non_reserved_inner + 1, pubkeys_hash_expected)
            bytecode_claims = Array(2)
            bytecode_claims[0] = non_reserved_inner + BYTECODE_CLAIM_OFFSET
            bytecode_claims[1] = recursion(inner_pub_mem, proof_transcript, bytecode_value_hint, inv_mds_16, inv_mds_24)
            reduce_bytecode_claims(bytecode_claims, 2, bytecode_claim_output, bytecode_sumcheck_proof)
            return

    # Hash pubkeys via Poseidon24 sponge: capacity(9) || root(8) || pp(5) || zeros(2)
    pk_hash_cap: Mut = Array(9)
    set_to_9_zeros(pk_hash_cap)
    for i in range(0, n_sigs):
        pk = all_pubkeys + i * PUBKEY_SIZE
        rate = Array(15)
        copy_8(pk, rate)
        copy_5(pk + DIGEST_LEN, rate + 8)
        rate[13] = 0
        rate[14] = 0
        new_cap = Array(9)
        poseidon24(pk_hash_cap, rate, new_cap)
        pk_hash_cap = new_cap
    copy_8(pk_hash_cap, pubkeys_hash_expected)

    # Buffer for partition verification
    n_total = n_sigs + n_dup
    buffer = Array(n_total)
    counter: Mut = 0

    # Raw XMSS source (source 0)
    raw_indices = source_0 + 1

    for i in range(0, n_raw_xmss):  # TODO dynamic unroll ?
        # mark buffer for partition verification
        idx = raw_indices[i]
        assert idx < n_total
        buffer[idx] = counter
        counter += 1
        # Verify raw XMSS signatures
        pk = all_pubkeys + idx * PUBKEY_SIZE
        pp = pk + DIGEST_LEN
        sig = Array(SIG_SIZE)
        hint_xmss(sig)
        xmss_verify(pk, pp, message, sig, all_tweaks, merkle_chunks_for_slot)

    # Recursive sources
    n_bytecode_claims = n_recursions * 2
    bytecode_claims = Array(n_bytecode_claims)

    for rec_idx in range(0, n_recursions):
        source_data = sub_slice_starts[rec_idx + 1]
        n_sub = source_data[0]
        assert n_sub != 0
        assert n_sub < MAX_N_SIGS
        sub_indices = source_data + 1
        bytecode_value_hint = sub_indices + n_sub
        inner_pub_mem = bytecode_value_hint + DIM
        proof_transcript = inner_pub_mem + INNER_PUB_MEM_SIZE

        running_hash: Mut = Array(9)
        set_to_9_zeros(running_hash)
        for j in range(0, n_sub):
            idx = sub_indices[j]
            assert idx < n_total
            buffer[idx] = counter
            counter += 1
            pk = all_pubkeys + idx * PUBKEY_SIZE
            rate = Array(15)
            copy_8(pk, rate)
            copy_5(pk + DIGEST_LEN, rate + 8)
            rate[13] = 0
            rate[14] = 0
            new_cap = Array(9)
            poseidon24(running_hash, rate, new_cap)
            running_hash = new_cap

        non_reserved_inner = verify_inner_pub_mem(inner_pub_mem, n_sub, message, slot_lo, slot_hi, merkle_chunks_for_slot, all_tweaks, pub_mem)
        copy_8(running_hash, non_reserved_inner + 1)

        # Collect inner bytecode claim from inner pub mem
        bytecode_claims[2 * rec_idx] = non_reserved_inner + BYTECODE_CLAIM_OFFSET

        # Verify recursive proof - returns the second bytecode claim
        bytecode_claims[2 * rec_idx + 1] = recursion(inner_pub_mem, proof_transcript, bytecode_value_hint, inv_mds_16, inv_mds_24)

    # Ensure partition validity
    assert counter == n_total

    # Bytecode claims
    if n_recursions == 0:
        for k in unroll(0, BYTECODE_POINT_N_VARS):
            set_to_5_zeros(bytecode_claim_output + k * DIM)
        bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM] = BYTECODE_ZERO_EVAL
        for k in unroll(1, DIM):
            bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM + k] = 0
    else:
        reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output, bytecode_sumcheck_proof)
    return

def reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output, bytecode_sumcheck_proof):
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


def verify_inner_pub_mem(inner_pub_mem, n_sub, message, slot_lo, slot_hi, merkle_chunks_for_slot, all_tweaks, pub_mem):
    debug_assert(NONRESERVED_PROGRAM_INPUT_START % DIM == 0)
    for i in unroll(0, NONRESERVED_PROGRAM_INPUT_START / DIM):
        copy_5(i * DIM, inner_pub_mem + i * DIM)
    non_reserved_inner = inner_pub_mem + NONRESERVED_PROGRAM_INPUT_START
    assert non_reserved_inner[0] == n_sub
    inner_msg = non_reserved_inner + 1 + DIGEST_LEN
    debug_assert(MESSAGE_LEN <= 2 * DIM)
    copy_5(message, inner_msg)
    copy_5(message + (MESSAGE_LEN - DIM), inner_msg + (MESSAGE_LEN - DIM))
    inner_msg[MESSAGE_LEN] = slot_lo
    inner_msg[MESSAGE_LEN + 1] = slot_hi
    for k in unroll(0, N_MERKLE_CHUNKS):
        inner_msg[MESSAGE_LEN + 2 + k] = merkle_chunks_for_slot[k]
    # Copy all pre-computed tweaks to inner pub mem (786 FE = 157*5 + 1)
    inner_all_tweaks = inner_msg + MESSAGE_LEN + 2 + N_MERKLE_CHUNKS
    n_tweak_copy5 = (N_ALL_TWEAKS - N_ALL_TWEAKS % DIM) / DIM
    for k in unroll(0, n_tweak_copy5):
        copy_5(all_tweaks + k * DIM, inner_all_tweaks + k * DIM)
    inner_all_tweaks[n_tweak_copy5 * DIM] = all_tweaks[n_tweak_copy5 * DIM]
    own_bytecode_hash = pub_mem + BYTECODE_HASH_OFFSET
    copy_8(own_bytecode_hash, non_reserved_inner + BYTECODE_HASH_OFFSET)
    return non_reserved_inner
