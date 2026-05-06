from recursion import *
from xmss_aggregate import *

MAX_RECURSIONS = MAX_RECURSIONS_PLACEHOLDER
MAX_N_SIGS = MAX_XMSS_AGGREGATED_PLACEHOLDER
MAX_N_DUPS = MAX_XMSS_DUPLICATES_PLACEHOLDER

# data_buf[0..8] = [flag, count, 0×6] (count = n_sigs for type-1, n_components for type-2).
TYPE_1_FLAG = TYPE_1_FLAG_PLACEHOLDER
TYPE_2_FLAG = TYPE_2_FLAG_PLACEHOLDER

BYTECODE_SUMCHECK_PROOF_SIZE = BYTECODE_SUMCHECK_PROOF_SIZE_PLACEHOLDER

# layout: [flag, count, 0×6 (8)] [bytecode_claim_padded] [bytecode_hash_domsep(8)] [type1/type2 mode-specific data]
BYTECODE_CLAIM_OFFSET = DIGEST_LEN  # (right after the prefix chunk)
BYTECODE_HASH_DOMSEP_OFFSET = BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE_PADDED
COMPONENT_DATA_OFFSET = BYTECODE_HASH_DOMSEP_OFFSET + DIGEST_LEN

# Type-1 mode-specific data (fixed): pubkeys_hash | message | merkle_chunks | tweaks_hash.
TYPE_1_PUBKEYS_HASH_OFFSET = COMPONENT_DATA_OFFSET
TYPE_1_MSG_HASH_OFFSET = COMPONENT_DATA_OFFSET + DIGEST_LEN
TYPE_1_MERKLE_CHUNKS_OFFSET = TYPE_1_MSG_HASH_OFFSET + DIGEST_LEN
TYPE_1_TWEAKS_HASH_OFFSET = TYPE_1_MERKLE_CHUNKS_OFFSET + N_MERKLE_CHUNKS
TYPE_1_INPUT_DATA_SIZE_PADDED = TYPE_1_TWEAKS_HASH_OFFSET + DIGEST_LEN
TYPE_1_INPUT_DATA_NUM_CHUNKS = TYPE_1_INPUT_DATA_SIZE_PADDED / DIGEST_LEN

# Type-2 mode-specific data (variable): n_components × digest(8).
TYPE_2_DIGESTS_OFFSET = COMPONENT_DATA_OFFSET

BYTECODE_CLAIM_NUM_CHUNKS = BYTECODE_CLAIM_SIZE_PADDED / DIGEST_LEN
TYPE_2_BASE_NUM_CHUNKS = BYTECODE_CLAIM_NUM_CHUNKS + 2  # prefix chunk + domsep chunk

def main():
    debug_assert(MAX_N_SIGS + MAX_N_DUPS <= 2**16)  # because of range checking, TODO increase
    pub_mem = 0  # See hashing.py for the memory layout
    build_preamble_memory()

    input_data_num_chunks_buf = Array(1)
    hint_witness("input_data_num_chunks", input_data_num_chunks_buf)
    input_data_num_chunks = input_data_num_chunks_buf[0]
    data_buf = Array(input_data_num_chunks * DIGEST_LEN)
    hint_witness("input_data", data_buf)
    set_to_6_zeros(data_buf + 2)

    bytecode_claim_output = data_buf + BYTECODE_CLAIM_OFFSET
    bytecode_hash_domsep = data_buf + BYTECODE_HASH_DOMSEP_OFFSET

    discriminator = data_buf[0]
    if discriminator == TYPE_2_FLAG:
        # Type-2: merge of n type-1 multi-signatures.
        n_components = data_buf[1]
        assert n_components != 0
        assert n_components <= MAX_RECURSIONS

        n_bytecode_claims = n_components * 2
        bytecode_claims = Array(n_bytecode_claims)

        for c in range(0, n_components):
            component_digest = data_buf + TYPE_2_DIGESTS_OFFSET + c * DIGEST_LEN
            inner_type1_buf = Array(TYPE_1_INPUT_DATA_SIZE_PADDED)
            hint_witness("component_layout", inner_type1_buf)
            ensure_well_formed_input_data(inner_type1_buf, bytecode_hash_domsep, TYPE_1_FLAG)
            slice_hash_with_iv(inner_type1_buf, TYPE_1_INPUT_DATA_NUM_CHUNKS, component_digest)

            bytecode_claims[2 * c] = inner_type1_buf + BYTECODE_CLAIM_OFFSET
            bytecode_claims[2 * c + 1] = recursion(component_digest, bytecode_hash_domsep)

        reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output)

        slice_hash_with_iv_range(data_buf, n_components + TYPE_2_BASE_NUM_CHUNKS, pub_mem)
        return

    assert discriminator == TYPE_1_FLAG

    is_split_buf = Array(1)
    hint_witness("is_split", is_split_buf)
    if is_split_buf[0] == 1:
        # ============ type-1: Split (extract a type-one from a type-two) ============
        type2_meta_hint = Array(2)
        hint_witness("type2_meta", type2_meta_hint)
        type2_n_components = type2_meta_hint[0]
        type2_kept_index = type2_meta_hint[1]
        assert type2_n_components != 0
        assert type2_n_components <= MAX_RECURSIONS
        assert type2_kept_index < type2_n_components

        type2_num_chunks = type2_n_components + TYPE_2_BASE_NUM_CHUNKS
        type2_data_buf = Array(type2_num_chunks * DIGEST_LEN)
        hint_witness("inner_type2_layout", type2_data_buf)
        ensure_well_formed_input_data(type2_data_buf, bytecode_hash_domsep, TYPE_2_FLAG)
        type2_digests = type2_data_buf + TYPE_2_DIGESTS_OFFSET
     
        kept_type1_buff = Array(TYPE_1_INPUT_DATA_SIZE_PADDED)
        hint_witness("kept_type1_buff", kept_type1_buff)
        copy_8(data_buf, kept_type1_buff) # type-1 flag | n_signatures | 0×6
        copy_32(data_buf + COMPONENT_DATA_OFFSET, kept_type1_buff + COMPONENT_DATA_OFFSET )
        ensure_well_formed_input_data(kept_type1_buff, bytecode_hash_domsep, TYPE_1_FLAG)
        digest_kept = type2_digests + type2_kept_index * DIGEST_LEN
        slice_hash_with_iv(kept_type1_buff, TYPE_1_INPUT_DATA_NUM_CHUNKS, digest_kept)

        inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
        slice_hash_with_iv_range(type2_data_buf, type2_num_chunks, inner_pub_mem)
        bytecode_claims = Array(2)
        bytecode_claims[0] = type2_data_buf + BYTECODE_CLAIM_OFFSET
        bytecode_claims[1] = recursion(inner_pub_mem, bytecode_hash_domsep)
        reduce_bytecode_claims(bytecode_claims, 2, bytecode_claim_output)
        slice_hash_with_iv(data_buf, TYPE_1_INPUT_DATA_NUM_CHUNKS, pub_mem)
        return

    # ============ Standard type-1: single (message, slot) aggregation ============
    n_sigs = data_buf[1]
    assert n_sigs != 0
    assert n_sigs - 1 < MAX_N_SIGS

    tweak_table: Mut = TWEAK_TABLE_ADDR
    hint_witness("tweak_table", tweak_table)

    pubkeys_hash_expected = data_buf + TYPE_1_PUBKEYS_HASH_OFFSET
    message = data_buf + TYPE_1_MSG_HASH_OFFSET
    merkle_chunks_for_slot = data_buf + TYPE_1_MERKLE_CHUNKS_OFFSET
    tweaks_hash_expected = data_buf + TYPE_1_TWEAKS_HASH_OFFSET

    # meta = [n_recursions, n_dup, n_raw_xmss]
    meta = Array(4)
    hint_witness("meta", meta)
    n_recursions = meta[0]
    assert n_recursions <= MAX_RECURSIONS

    n_dup = meta[1]
    assert n_dup < MAX_N_DUPS  # TODO increase

    all_pubkeys = Array((n_sigs + n_dup) * PUB_KEY_SIZE)
    hint_witness("pubkeys", all_pubkeys)
    n_raw_xmss = meta[2]
    raw_indices = Array(n_raw_xmss)
    hint_witness("raw_indices", raw_indices)

    aggregate_sizes = Array(n_recursions)
    hint_witness("aggregate_sizes", aggregate_sizes)

    computed_tweaks_hash = slice_hash(tweak_table, TWEAK_TABLE_SIZE_FE_PADDED / DIGEST_LEN)
    copy_8(computed_tweaks_hash, tweaks_hash_expected)

    # 1->1 optimization: a single recursive type-1 child, no raw signatures, no duplicates.
    if n_recursions == 1:
        assert n_dup == 0
        if n_raw_xmss == 0:
            type1_data_buf = Array(TYPE_1_INPUT_DATA_SIZE_PADDED)
            copy_8(data_buf, type1_data_buf)  # prefix
            copy_32(data_buf + COMPONENT_DATA_OFFSET, type1_data_buf + COMPONENT_DATA_OFFSET )
            hint_witness("inner_bytecode_claim", type1_data_buf + BYTECODE_CLAIM_OFFSET)
            ensure_well_formed_input_data(type1_data_buf, bytecode_hash_domsep, TYPE_1_FLAG)
            inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
            slice_hash_with_iv(type1_data_buf, TYPE_1_INPUT_DATA_NUM_CHUNKS, inner_pub_mem)
            bytecode_claims = Array(2)
            bytecode_claims[0] = type1_data_buf + BYTECODE_CLAIM_OFFSET
            bytecode_claims[1] = recursion(inner_pub_mem, bytecode_hash_domsep)
            reduce_bytecode_claims(bytecode_claims, 2, bytecode_claim_output)
            slice_hash_with_iv(data_buf, TYPE_1_INPUT_DATA_NUM_CHUNKS, pub_mem)
            return

    # General path
    computed_pubkeys_hash = slice_hash_with_iv_dynamic_unroll(all_pubkeys, n_sigs, log2_ceil(MAX_N_SIGS))
    copy_8(computed_pubkeys_hash, pubkeys_hash_expected)

    # Buffer for partition verification
    n_total = n_sigs + n_dup
    buffer = Array(n_total)

    for i in parallel_range(0, n_raw_xmss):
        idx = raw_indices[i]
        assert idx < n_total
        buffer[idx] = i
        pk = all_pubkeys + idx * PUB_KEY_SIZE
        xmss_verify(pk, message, merkle_chunks_for_slot)

    counter: Mut = n_raw_xmss

    n_bytecode_claims = n_recursions * 2
    bytecode_claims = Array(n_bytecode_claims)

    for rec_idx in range(0, n_recursions):
        n_sub = aggregate_sizes[rec_idx]
        assert n_sub != 0
        assert n_sub < MAX_N_SIGS
        sub_indices_arr = Array(n_sub)
        hint_witness("sub_indices", sub_indices_arr)

        idx0 = sub_indices_arr[0]
        assert idx0 < n_total
        buffer[idx0] = counter
        counter += 1
        pk0 = all_pubkeys + idx0 * PUB_KEY_SIZE
        running_hash: Mut = Array(DIGEST_LEN)
        poseidon16_compress(ZERO_VEC_PTR, pk0, running_hash)

        for j in dynamic_unroll(1, n_sub, log2_ceil(MAX_N_SIGS)):
            idx = sub_indices_arr[j]
            assert idx < n_total
            buffer[idx] = counter
            counter += 1
            pk = all_pubkeys + idx * PUB_KEY_SIZE
            new_hash = Array(DIGEST_LEN)
            poseidon16_compress(running_hash, pk, new_hash)
            running_hash = new_hash

        type1_data_buf = Array(TYPE_1_INPUT_DATA_SIZE_PADDED)
        type1_data_buf[0] = TYPE_1_FLAG
        type1_data_buf[1] = n_sub
        for k in unroll(2, DIGEST_LEN):
            type1_data_buf[k] = 0
        
        copy_8(running_hash, type1_data_buf + TYPE_1_PUBKEYS_HASH_OFFSET)
        copy_8(message, type1_data_buf + TYPE_1_PUBKEYS_HASH_OFFSET + DIGEST_LEN)
        copy_8(merkle_chunks_for_slot, type1_data_buf + TYPE_1_PUBKEYS_HASH_OFFSET + DIGEST_LEN + MESSAGE_LEN)
        copy_8(tweaks_hash_expected, type1_data_buf + TYPE_1_TWEAKS_HASH_OFFSET)
        hint_witness("inner_bytecode_claim", type1_data_buf + BYTECODE_CLAIM_OFFSET)
        ensure_well_formed_input_data(type1_data_buf, bytecode_hash_domsep, TYPE_1_FLAG)
        inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
        slice_hash_with_iv(type1_data_buf, TYPE_1_INPUT_DATA_NUM_CHUNKS, inner_pub_mem)

        bytecode_claims[2 * rec_idx] = type1_data_buf + BYTECODE_CLAIM_OFFSET
        bytecode_claims[2 * rec_idx + 1] = recursion(inner_pub_mem, bytecode_hash_domsep)

    assert counter == n_total

    if n_recursions == 0:
        for k in unroll(0, BYTECODE_POINT_N_VARS):
            set_to_5_zeros(bytecode_claim_output + k * DIM)
        bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM] = BYTECODE_ZERO_EVAL
        for k in unroll(1, DIM):
            bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM + k] = 0
    else:
        reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output)

    slice_hash_with_iv(data_buf, TYPE_1_INPUT_DATA_NUM_CHUNKS, pub_mem)
    return


def reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output):
    bytecode_claims_hash: Mut = ZERO_VEC_PTR
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
            assert claim_ptr[k] == 0
        claim_hash = slice_hash(claim_ptr, BYTECODE_CLAIM_SIZE_PADDED / DIGEST_LEN)
        new_hash = Array(DIGEST_LEN)
        poseidon16_compress(bytecode_claims_hash, claim_hash, new_hash)
        bytecode_claims_hash = new_hash

    bytecode_sumcheck_proof = Array(BYTECODE_SUMCHECK_PROOF_SIZE)
    hint_witness("bytecode_sumcheck_proof", bytecode_sumcheck_proof)
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

    eq_evals = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        poly_eq_ee(claim_ptr, challenges, eq_evals + i * DIM, BYTECODE_POINT_N_VARS)
    w_r = Array(DIM)
    dot_product_ee_dynamic(eq_evals, alpha_powers, w_r, n_bytecode_claims)

    bytecode_value_at_r = div_extension_ret(final_eval, w_r)

    copy_many_ef(challenges, bytecode_claim_output, BYTECODE_POINT_N_VARS)
    copy_5(bytecode_value_at_r, bytecode_claim_output + BYTECODE_POINT_N_VARS * DIM)
    return


@inline
def ensure_well_formed_input_data(data_buf, bytecode_hash_domsep, flag):
    data_buf[0] = flag
    # data_buf[1]: count
    set_to_6_zeros(data_buf + 2)
    for k in unroll(BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE, BYTECODE_HASH_DOMSEP_OFFSET):
        data_buf[k] = 0
    copy_8(bytecode_hash_domsep, data_buf + BYTECODE_HASH_DOMSEP_OFFSET)
    return
