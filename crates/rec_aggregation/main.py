from recursion import *
from xmss_aggregate import *

MAX_RECURSIONS = 16

# TODO increase (we would need a bigger minimal memory size, totally doable)
MAX_N_SIGS = 2**15
MAX_N_DUPS = 2**15

INNER_PUB_MEM_SIZE = 2**INNER_PUBLIC_MEMORY_LOG_SIZE
PRIVATE_INPUT_START = INNER_PUB_MEM_SIZE

INPUT_DATA_SIZE_PADDED = INPUT_DATA_SIZE_PADDED_PLACEHOLDER
INPUT_DATA_NUM_CHUNKS = INPUT_DATA_SIZE_PADDED / DIGEST_LEN
BYTECODE_CLAIM_OFFSET = 1 + DIGEST_LEN + MESSAGE_LEN + N_MERKLE_CHUNKS + N_ALL_TWEAKS
BYTECODE_HASH_DOMSEP_OFFSET = BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE_PADDED


def main():
    debug_assert(MAX_N_SIGS + MAX_N_DUPS <= 2**16)  # because of range checking, TODO increase
    pub_mem = NONRESERVED_PROGRAM_INPUT_START

    data_buf: Mut = PRIVATE_INPUT_START # Mut is a trick to force the compiler to put it in memory (TODO improve this)
    n_sigs = data_buf[0]
    assert n_sigs != 0
    assert n_sigs - 1 < MAX_N_SIGS
    pubkeys_hash_expected = data_buf + 1
    message = pubkeys_hash_expected + DIGEST_LEN
    merkle_chunks_for_slot = message + MESSAGE_LEN
    all_tweaks = merkle_chunks_for_slot + N_MERKLE_CHUNKS
    bytecode_claim_output = data_buf + BYTECODE_CLAIM_OFFSET
    bytecode_hash_domsep = data_buf + BYTECODE_HASH_DOMSEP_OFFSET

    header = PRIVATE_INPUT_START + INPUT_DATA_SIZE_PADDED

    n_recursions = header[0]
    assert n_recursions <= MAX_RECURSIONS

    n_dup = header[1]
    assert n_dup < MAX_N_SIGS  # TODO increase
    all_pubkeys = header[2]
    sub_slice_starts = header + 3
    bytecode_sumcheck_proof = sub_slice_starts[n_recursions + 1]

    source_0 = sub_slice_starts[0]
    n_raw_xmss = source_0[0]

    # 1->1 optimization
    if n_recursions == 1:
        assert n_dup == 0
        if n_raw_xmss == 0:
            source_data = sub_slice_starts[1]
            n_sub = source_data[0]
            assert n_sub != 0
            assert n_sub == n_sigs
            bytecode_value_hint = source_data + 1 + n_sub
            inner_data_buf = bytecode_value_hint + DIM
            proof_transcript = inner_data_buf + INPUT_DATA_SIZE_PADDED
            inner_bytecode_claim = inner_data_buf + BYTECODE_CLAIM_OFFSET
            copy_8(pubkeys_hash_expected, inner_data_buf + 1)
            stage_inner_data_buf(inner_data_buf, n_sub, message, merkle_chunks_for_slot, all_tweaks, bytecode_hash_domsep)
            inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
            construct_inner_pub_mem(inner_pub_mem, inner_data_buf)
            bytecode_claims = Array(2)
            bytecode_claims[0] = inner_bytecode_claim
            bytecode_claims[1] = recursion(inner_pub_mem, proof_transcript, bytecode_value_hint, bytecode_hash_domsep)
            reduce_bytecode_claims(bytecode_claims, 2, bytecode_claim_output, bytecode_sumcheck_proof)
            # All fields of `data_buf` are now written: hash it and assert the digest
            # matches the (single-element) public input by writing into public memory.
            outer_hash = slice_hash_with_iv(data_buf, INPUT_DATA_NUM_CHUNKS)
            copy_8(outer_hash, pub_mem)
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
        poseidon24_compress_0_9(pk_hash_cap, rate, new_cap)
        pk_hash_cap = new_cap
    copy_8(pk_hash_cap, pubkeys_hash_expected)

    # Buffer for partition verification
    n_total = n_sigs + n_dup
    buffer = Array(n_total)

    # Raw XMSS source (source 0)
    raw_indices = source_0 + 1

    for i in parallel_range(0, n_raw_xmss):
        # mark buffer for partition verification
        idx = raw_indices[i]
        assert idx < n_total
        buffer[idx] = i
        # Verify raw XMSS signatures
        pk = all_pubkeys + idx * PUBKEY_SIZE
        pp = pk + DIGEST_LEN
        sig = Array(SIG_SIZE)
        hint_xmss(sig)
        xmss_verify(pk, pp, message, sig, all_tweaks, merkle_chunks_for_slot)

    counter: Mut = n_raw_xmss

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
        inner_data_buf = bytecode_value_hint + DIM
        proof_transcript = inner_data_buf + INPUT_DATA_SIZE_PADDED

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
            poseidon24_compress_0_9(running_hash, rate, new_cap)
            running_hash = new_cap

        copy_8(running_hash, inner_data_buf + 1) # hash of pubkeys handled by this recursion
        stage_inner_data_buf(inner_data_buf, n_sub, message, merkle_chunks_for_slot, all_tweaks, bytecode_hash_domsep)
        inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
        construct_inner_pub_mem(inner_pub_mem, inner_data_buf)

        bytecode_claims[2 * rec_idx] = inner_data_buf + BYTECODE_CLAIM_OFFSET

        # Verify recursive proof - returns the second bytecode claim
        bytecode_claims[2 * rec_idx + 1] = recursion(inner_pub_mem, proof_transcript, bytecode_value_hint, bytecode_hash_domsep)

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

    # All fields of `data_buf` are now written: hash it and assert the digest
    # matches the (single-element) public input by writing into public memory.
    outer_hash = slice_hash_with_iv(data_buf, INPUT_DATA_NUM_CHUNKS)
    copy_8(outer_hash, pub_mem)
    return

def reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output, bytecode_sumcheck_proof):
    bytecode_claims_hash: Mut = ZERO_VEC_PTR
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
            assert claim_ptr[k] == 0
        claim_hash = slice_hash(claim_ptr, BYTECODE_CLAIM_SIZE_PADDED / DIGEST_LEN)
        new_hash = Array(DIGEST_LEN)
        poseidon16_compress(bytecode_claims_hash, claim_hash, new_hash)
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


@inline
def stage_inner_data_buf(inner_data_buf, n_sub, message, merkle_chunks_for_slot, all_tweaks, bytecode_hash_domsep):
    inner_data_buf[0] = n_sub
    inner_msg = inner_data_buf + 1 + DIGEST_LEN
    debug_assert(MESSAGE_LEN <= 2 * DIM)
    copy_5(message, inner_msg)
    copy_5(message + (MESSAGE_LEN - DIM), inner_msg + (MESSAGE_LEN - DIM))
    for k in unroll(0, N_MERKLE_CHUNKS):
        inner_msg[MESSAGE_LEN + k] = merkle_chunks_for_slot[k]
    # Copy all pre-computed tweaks
    inner_all_tweaks = inner_msg + MESSAGE_LEN + N_MERKLE_CHUNKS
    n_tweak_copy5 = div_floor(N_ALL_TWEAKS, DIM)
    for k in unroll(0, n_tweak_copy5):
        copy_5(all_tweaks + k * DIM, inner_all_tweaks + k * DIM)
    for k in unroll(0, N_ALL_TWEAKS % DIM):
        inner_all_tweaks[n_tweak_copy5 * DIM + k] = all_tweaks[n_tweak_copy5 * DIM + k]
    for k in unroll(BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE, BYTECODE_HASH_DOMSEP_OFFSET):
        inner_data_buf[k] = 0
    copy_8(bytecode_hash_domsep, inner_data_buf + BYTECODE_HASH_DOMSEP_OFFSET)
    for k in unroll(BYTECODE_HASH_DOMSEP_OFFSET + DIGEST_LEN, INPUT_DATA_SIZE_PADDED):
        inner_data_buf[k] = 0
    return


@inline
def construct_inner_pub_mem(inner_pub_mem, inner_data_buf):
    debug_assert(NONRESERVED_PROGRAM_INPUT_START % DIM == 0)
    for i in unroll(0, NONRESERVED_PROGRAM_INPUT_START / DIM):
        copy_5(i * DIM, inner_pub_mem + i * DIM)
    # Non-reserved area: the inner data digest...
    inner_hash = slice_hash_with_iv(inner_data_buf, INPUT_DATA_NUM_CHUNKS)
    copy_8(inner_hash, inner_pub_mem + NONRESERVED_PROGRAM_INPUT_START)
    # ...followed by zeros up to INNER_PUB_MEM_SIZE: as many DIM-wide
    # set_to_5_zeros as fit, then field-by-field for the leftover.
    tail_start = NONRESERVED_PROGRAM_INPUT_START + DIGEST_LEN
    tail_full_chunks = div_floor(INNER_PUB_MEM_SIZE - tail_start, DIM)
    for c in unroll(0, tail_full_chunks):
        set_to_5_zeros(inner_pub_mem + tail_start + c * DIM)
    for k in unroll(tail_start + tail_full_chunks * DIM, INNER_PUB_MEM_SIZE):
        inner_pub_mem[k] = 0
    return
