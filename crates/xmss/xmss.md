# XMSS high-level specification

## Field

p = 125.2^25 + 1

## Hash function

[Poseidon](https://eprint.iacr.org/2019/458), in compression mode (feedforward addition). Input: 16 field elements. Output: 8 field elements. We denote it `H`. Chain hashes, Merkle hashes, and the final WOTS-pubkey hash truncate the output to 4 field elements (`n`); the encoding step and the intermediate WOTS-pubkey sponge states keep the full 8 elements.

## Sizes (in field elements)

- `n = 4`: digest size
- `|pp| = 4`: public parameter
- `|randomness| = 6`: signature randomness
- `|msg| = 8`: message size
- `|tweak| = 2`: tweak (domain separation: `encoding`, `chain`, `wots_pk`, `merkle`)

## WOTS (Winternitz One Time Signature)

- `v = 42`: number of hash chains
- `w = 3`, `chain_length = 2^w = 8`
- `target_sum = 184`: a WOTS encoding `(e_0, ..., e_{v-1})` is valid iff each `e_i < chain_length` and `sum(e_i) = target_sum`. The signer grinds `randomness` until the encoding is valid (avoids checksum chains).
- `encoding_num_final_zeros = 2`: the `encoding_num_final_zeros` bits of the encoding digest immediately after the `v · w = 126` chain-encoding bits must be zero (for 128-bits security)

## XMSS

`log_lifetime = 32`: a key is valid for up to `2^32` slots. `log_lifetime` corresponds to the Merkle tree height.

## Verification

Inputs: public key `(merkle_root, pp)`, message `msg`, slot `s`, signature `(randomness, chain_tips, merkle_proof)`.

1. **Encode**: compute the 8-limb digest `D = H(H(msg | randomness | tweak_encoding(s)) | pp | 0000)`. Reject if any limb of `D` equals `-1` (for a uniform sampling). For each limb, take its canonical representative's low 24 bits in little-endian order, concatenate to get 192 bits. Reject if any of the `encoding_num_final_zeros` bits at positions `v · w .. v · w + encoding_num_final_zeros` is non-zero. Take the first `v · w = 126` bits split into `v = 42` little-endian chunks of `w = 3` bits → encoding `(e_0, ..., e_{v-1})` with each `e_i ∈ [0, chain_length)`. Reject if `sum(e_i) ≠ target_sum`.
2. **Recover WOTS public key**: for each `i`, walk chain `i` from `chain_tips[i]` for `chain_length - 1 - e_i` steps, where each step is `H(tweak_chain(i, step, s) | 00 | previous_value | pp | 0000)` truncated to `n`.
3. **Hash WOTS public key**: T-sponge with replacement over the `v` recovered chain ends, with IV `[tweak_wots_pk(s) | 00 | pp]`, ingesting two chain end digests at a time. Output is the Merkle leaf.
4. **Walk Merkle path**: for `level = 0..log_lifetime`, combine the current node with `merkle_proof[level]` (left/right determined by bit `level` of `s`) via `H(tweak_merkle(level+1, parent_index) | 00 | pp | left | right)` truncated to `n`.
5. **Check root**: accept iff the final hash equals `merkle_root`.


## Security

target = 127.84 ≈ 128 bits of classical security in the ROM, and ≈ 64 bits of quantum security in the QROM, with an analysis inspired by the section 3.1 of [Tight adaptive reprogramming in the QROM](https://arxiv.org/pdf/2010.15103). TODO write the complete proof.

## Signature size

**1171 bytes** `log2(p).(|randomness| + n.(v + log_lifetime))`

below IPv6 [MTU](https://fr.wikipedia.org/wiki/Maximum_transmission_unit) (1280 bytes)
