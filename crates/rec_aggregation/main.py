from recursion import *
from xmss_aggregate import *

# ===================== Type-1 constants =====================
MAX_RECURSIONS = 16
# TODO increase (we would need a bigger minimal memory size, totally doable)
MAX_N_SIGS = 2**15
MAX_N_DUPS = 2**15

TYPE2_MAX_COMPONENTS = TYPE2_MAX_COMPONENTS_PLACEHOLDER
TYPE2_DISCRIMINATOR = TYPE2_DISCRIMINATOR_PLACEHOLDER
#   n_sigs(1) + pubkeys_hash(8) + message(8) + merkle_chunks_for_slot(8) + tweaks_hash(8)
COMPONENT_HEADER_SIZE = 1 + DIGEST_LEN + MESSAGE_LEN + N_MERKLE_CHUNKS + DIGEST_LEN

INPUT_DATA_SIZE_PADDED = INPUT_DATA_SIZE_PADDED_PLACEHOLDER
INPUT_DATA_NUM_CHUNKS = INPUT_DATA_SIZE_PADDED / DIGEST_LEN
BYTECODE_SUMCHECK_PROOF_SIZE = BYTECODE_SUMCHECK_PROOF_SIZE_PLACEHOLDER

# Type-1 layout (data_buf[0] = n_sigs).
#   n_sigs(1) + pubkeys_hash(8) + message(8) + merkle_chunks_for_slot(8)
#   + tweaks_hash(8) + bytecode_claim_padded + bytecode_hash_domsep(8)
TYPE1_TWEAKS_HASH_OFFSET = 1 + DIGEST_LEN + MESSAGE_LEN + N_MERKLE_CHUNKS
TYPE1_BYTECODE_CLAIM_OFFSET = TYPE1_TWEAKS_HASH_OFFSET + DIGEST_LEN
TYPE1_BYTECODE_HASH_DOMSEP_OFFSET = TYPE1_BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE_PADDED

# Type-2 layout (data_buf[0] = 0 sentinel; data_buf[1] = n_components).
#   zero_sentinel(1) + n_components(1) + MAX_COMPONENTS * COMPONENT_HEADER_SIZE
#   + bytecode_claim_padded + bytecode_hash_domsep(8)
TYPE2_HEADERS_OFFSET = 2
TYPE2_BYTECODE_CLAIM_OFFSET = TYPE2_HEADERS_OFFSET + TYPE2_MAX_COMPONENTS * COMPONENT_HEADER_SIZE
TYPE2_BYTECODE_HASH_DOMSEP_OFFSET = TYPE2_BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE_PADDED


def main():
    debug_assert(MAX_N_SIGS + MAX_N_DUPS <= 2**16)  # because of range checking, TODO increase
    pub_mem = 0  # See hashing.py for the memory layout
    build_preamble_memory()

    data_buf = Array(INPUT_DATA_SIZE_PADDED)
    hint_witness("input_data", data_buf)

    discriminator = data_buf[0]
    if discriminator == TYPE2_DISCRIMINATOR:
        # ============ Type-2: merge of n type-1 multi-signatures ============
        debug_assert(TYPE2_MAX_COMPONENTS <= 2**8)

        n_components = data_buf[1]
        assert n_components != 0
        assert n_components <= TYPE2_MAX_COMPONENTS

        bytecode_claim_output = data_buf + TYPE2_BYTECODE_CLAIM_OFFSET
        bytecode_hash_domsep = data_buf + TYPE2_BYTECODE_HASH_DOMSEP_OFFSET

        n_bytecode_claims = n_components * 2
        bytecode_claims = Array(n_bytecode_claims)

        for c in range(0, n_components):
            component_offset = TYPE2_HEADERS_OFFSET + c * COMPONENT_HEADER_SIZE
            component_header = data_buf + component_offset
            n_sigs_c = component_header[0]
            assert n_sigs_c != 0
            assert n_sigs_c - 1 < MAX_N_SIGS

            slice_hash_c = component_header + 1
            message_c = slice_hash_c + DIGEST_LEN
            merkle_chunks_c = message_c + MESSAGE_LEN
            tweaks_hash_c = merkle_chunks_c + N_MERKLE_CHUNKS

            inner_data_buf = build_inner_data_buf_type1(
                n_sigs_c, slice_hash_c, message_c, merkle_chunks_c, tweaks_hash_c, bytecode_hash_domsep,
            )
            inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
            copy_8(slice_hash_with_iv(inner_data_buf, INPUT_DATA_NUM_CHUNKS), inner_pub_mem)

            bytecode_claims[2 * c] = inner_data_buf + TYPE1_BYTECODE_CLAIM_OFFSET
            bytecode_claims[2 * c + 1] = recursion(inner_pub_mem, bytecode_hash_domsep)

        reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output)

        outer_hash = slice_hash_with_iv(data_buf, INPUT_DATA_NUM_CHUNKS)
        copy_8(outer_hash, pub_mem)
        return

    # ============ Type-1: existing single (message, slot) aggregation ============
    n_sigs = discriminator
    assert n_sigs - 1 < MAX_N_SIGS

    tweak_table: Mut = TWEAK_TABLE_ADDR
    hint_witness("tweak_table", tweak_table)

    pubkeys_hash_expected = data_buf + 1
    message = pubkeys_hash_expected + DIGEST_LEN
    merkle_chunks_for_slot = message + MESSAGE_LEN
    tweaks_hash_expected = data_buf + TYPE1_TWEAKS_HASH_OFFSET
    bytecode_claim_output = data_buf + TYPE1_BYTECODE_CLAIM_OFFSET
    bytecode_hash_domsep = data_buf + TYPE1_BYTECODE_HASH_DOMSEP_OFFSET

    # meta = [n_recursions, n_dup, pubkeys_len, n_raw_xmss]
    meta = Array(4)
    hint_witness("meta", meta)
    n_recursions = meta[0]
    assert n_recursions <= MAX_RECURSIONS

    n_dup = meta[1]
    assert n_dup < MAX_N_SIGS  # TODO increase

    all_pubkeys = Array(meta[2])
    hint_witness("pubkeys", all_pubkeys)
    n_raw_xmss = meta[3]
    raw_indices = Array(n_raw_xmss)
    hint_witness("raw_indices", raw_indices)

    aggregate_sizes = Array(n_recursions)
    hint_witness("aggregate_sizes", aggregate_sizes)

    computed_tweaks_hash = slice_hash(tweak_table, TWEAK_TABLE_SIZE_FE_PADDED / DIGEST_LEN)
    copy_8(computed_tweaks_hash, tweaks_hash_expected)

    # 1->1 optimization. Two flavors gated by the `is_inner_type2` hint:
    #  - 0 (default): the recursive child is itself a type-1 proof (existing behavior).
    #  - 1 (split): the recursive child is a type-2 proof; the verifier provides
    #    the OTHER components and the kept index as hints, and the bytecode
    #    reconstructs the type-2 outer hash before calling recursion().
    if n_recursions == 1:
        assert n_dup == 0
        if n_raw_xmss == 0:
            is_inner_type2_buf = Array(1)
            hint_witness("is_inner_type2", is_inner_type2_buf)
            if is_inner_type2_buf[0] == 0:
                inner_data_buf = build_inner_data_buf_type1(
                    n_sigs, pubkeys_hash_expected, message,
                    merkle_chunks_for_slot, tweaks_hash_expected, bytecode_hash_domsep,
                )
                inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
                copy_8(slice_hash_with_iv(inner_data_buf, INPUT_DATA_NUM_CHUNKS), inner_pub_mem)
                bytecode_claims = Array(2)
                bytecode_claims[0] = inner_data_buf + TYPE1_BYTECODE_CLAIM_OFFSET
                bytecode_claims[1] = recursion(inner_pub_mem, bytecode_hash_domsep)
                reduce_bytecode_claims(bytecode_claims, 2, bytecode_claim_output)
                outer_hash = slice_hash_with_iv(data_buf, INPUT_DATA_NUM_CHUNKS)
                copy_8(outer_hash, pub_mem)
                return
            else:
                # Split path: build a type-2-layout inner buffer that contains
                # the kept component (taken from data_buf) plus all OTHER
                # components (hinted), then recursively verify the type-2
                # SNARK against its hash.
                inner_data_buf = Array(INPUT_DATA_SIZE_PADDED)
                inner_data_buf[0] = TYPE2_DISCRIMINATOR

                type2_meta_hint = Array(2)
                hint_witness("type2_meta", type2_meta_hint)
                type2_n_components = type2_meta_hint[0]
                type2_kept_index = type2_meta_hint[1]
                inner_data_buf[1] = type2_n_components
                assert type2_n_components != 0
                assert type2_n_components - 1 < TYPE2_MAX_COMPONENTS

                type2_components = Array(TYPE2_MAX_COMPONENTS * COMPONENT_HEADER_SIZE)
                hint_witness("type2_components", type2_components)

                # Copy the (hinted) components into the type-2 layout positions.
                for c in unroll(0, TYPE2_MAX_COMPONENTS):
                    src = type2_components + c * COMPONENT_HEADER_SIZE
                    dst = inner_data_buf + TYPE2_HEADERS_OFFSET + c * COMPONENT_HEADER_SIZE
                    for k in unroll(0, COMPONENT_HEADER_SIZE):
                        dst[k] = src[k]

                # Bind: the kept-index slot in type2_components must match
                # data_buf's component-i fields (which span the first
                # COMPONENT_HEADER_SIZE entries of the type-1 outer layout).
                match_range(
                    type2_kept_index,
                    range(0, TYPE2_MAX_COMPONENTS),
                    lambda i: assert_components_kept_match(type2_components, data_buf, i),
                )

                hint_witness("inner_bytecode_claim", inner_data_buf + TYPE2_BYTECODE_CLAIM_OFFSET)
                for k in unroll(TYPE2_BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE, TYPE2_BYTECODE_HASH_DOMSEP_OFFSET):
                    inner_data_buf[k] = 0
                copy_8(bytecode_hash_domsep, inner_data_buf + TYPE2_BYTECODE_HASH_DOMSEP_OFFSET)
                for k in range(TYPE2_BYTECODE_HASH_DOMSEP_OFFSET + DIGEST_LEN, INPUT_DATA_SIZE_PADDED):
                    inner_data_buf[k] = 0

                inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
                copy_8(slice_hash_with_iv(inner_data_buf, INPUT_DATA_NUM_CHUNKS), inner_pub_mem)
                bytecode_claims = Array(2)
                bytecode_claims[0] = inner_data_buf + TYPE2_BYTECODE_CLAIM_OFFSET
                bytecode_claims[1] = recursion(inner_pub_mem, bytecode_hash_domsep)
                reduce_bytecode_claims(bytecode_claims, 2, bytecode_claim_output)
                outer_hash = slice_hash_with_iv(data_buf, INPUT_DATA_NUM_CHUNKS)
                copy_8(outer_hash, pub_mem)
                return

    # General path
    computed_pubkeys_hash = slice_hash_with_iv_dynamic_unroll(all_pubkeys, n_sigs * PUB_KEY_SIZE, MAX_LOG_MEMORY_SIZE)
    copy_8(computed_pubkeys_hash, pubkeys_hash_expected)

    # Buffer for partition verification
    n_total = n_sigs + n_dup
    buffer = Array(n_total)

    for i in parallel_range(0, n_raw_xmss):
        # mark buffer for partition verification
        idx = raw_indices[i]
        assert idx < n_total
        buffer[idx] = i
        # Verify raw XMSS signatures.
        pk = all_pubkeys + idx * PUB_KEY_SIZE
        xmss_verify(pk, message, merkle_chunks_for_slot)

    counter: Mut = n_raw_xmss

    # Recursive sources
    n_bytecode_claims = n_recursions * 2
    bytecode_claims = Array(n_bytecode_claims)

    for rec_idx in range(0, n_recursions):
        sub_indices_blob = Array(aggregate_sizes[rec_idx])
        hint_witness("sub_indices", sub_indices_blob)
        n_sub = sub_indices_blob[0]
        assert n_sub != 0
        assert n_sub < MAX_N_SIGS
        sub_indices_arr = sub_indices_blob + 1

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

        inner_data_buf = build_inner_data_buf_type1(
            n_sub, running_hash, message,
            merkle_chunks_for_slot, tweaks_hash_expected, bytecode_hash_domsep,
        )
        inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
        copy_8(slice_hash_with_iv(inner_data_buf, INPUT_DATA_NUM_CHUNKS), inner_pub_mem)

        bytecode_claims[2 * rec_idx] = inner_data_buf + TYPE1_BYTECODE_CLAIM_OFFSET
        # Verify recursive proof - returns the second bytecode claim
        bytecode_claims[2 * rec_idx + 1] = recursion(inner_pub_mem, bytecode_hash_domsep)

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
        reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output)

    outer_hash = slice_hash_with_iv(data_buf, INPUT_DATA_NUM_CHUNKS)
    copy_8(outer_hash, pub_mem)
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

    # Verify: final_eval == bytecode(r) * w(r)
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
def build_inner_data_buf_type1(n_sub, pubkeys_hash, message, merkle_chunks_for_slot, tweaks_hash, bytecode_hash_domsep):
    # Inner buffer is type-1-formatted (the recursive child is always type-1),
    # but lives in a unified-size buffer so its hash matches the public-input
    # digest the verifier computes for a type-1 proof.
    inner_data_buf = Array(INPUT_DATA_SIZE_PADDED)
    inner_data_buf[0] = n_sub
    copy_8(pubkeys_hash, inner_data_buf + 1)
    inner_msg = inner_data_buf + 1 + DIGEST_LEN
    copy_8(message, inner_msg)
    for k in unroll(0, N_MERKLE_CHUNKS):
        inner_msg[MESSAGE_LEN + k] = merkle_chunks_for_slot[k]
    copy_8(tweaks_hash, inner_data_buf + TYPE1_TWEAKS_HASH_OFFSET)
    hint_witness("inner_bytecode_claim", inner_data_buf + TYPE1_BYTECODE_CLAIM_OFFSET)
    for k in unroll(TYPE1_BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE, TYPE1_BYTECODE_HASH_DOMSEP_OFFSET):
        inner_data_buf[k] = 0
    copy_8(bytecode_hash_domsep, inner_data_buf + TYPE1_BYTECODE_HASH_DOMSEP_OFFSET)
    # Zero out the unused tail (everything past the type-1 fields). With a
    # unified buffer that's much larger than type-1 needs, we use a runtime
    # loop here to keep the bytecode size bounded.
    for k in range(TYPE1_BYTECODE_HASH_DOMSEP_OFFSET + DIGEST_LEN, INPUT_DATA_SIZE_PADDED):
        inner_data_buf[k] = 0
    return inner_data_buf


def assert_components_kept_match(components_blob, data_buf, kept_idx: Const):
    # In split mode, data_buf is laid out in the type-1 format for the kept
    # component, which matches a single COMPONENT_HEADER (n_sigs, slice_hash,
    # message, merkle_chunks_for_slot, tweaks_hash) byte-for-byte at offset 0.
    for k in unroll(0, COMPONENT_HEADER_SIZE):
        assert components_blob[kept_idx * COMPONENT_HEADER_SIZE + k] == data_buf[k]
    return
