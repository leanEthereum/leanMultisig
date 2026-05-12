# XMSS high-level specification

## Field

Goldilocks (p = 2^64 - 2^32 + 1).

## Hash function

[Poseidon](https://eprint.iacr.org/2019/458), in compression mode (feedforward addition). Input: 8 field elements. Output: 4 field elements. We denote it `H`. Chain hashes, Merkle hashes, and the final WOTS-pubkey hash truncate the output to 2 field elements (`n`); the encoding step and the intermediate WOTS-pubkey sponge states keep the full 4 elements.

## Sizes (in field elements)

- `n = 2`: digest size
- `|pp| = 2`: public parameter
- `|randomness| = 3`: signature randomness
- `|msg| = 4`: message size
- `|tweak| = 1`: tweak (domain separation: `encoding`, `chain`, `wots_pk`, `merkle`)

## WOTS (Winternitz One Time Signature)

- `v = 40`: number of hash chains
- `w = 3`, `chain_length = 2^w = 8`
- `target_sum = 170`: a WOTS encoding `(e_0, ..., e_{v-1})` is valid iff each `e_i < chain_length` and `sum(e_i) = target_sum`. The signer grinds `randomness` until the encoding is valid (avoids checksum chains).
- `encoding_num_final_zeros = 8`: the 2 high bits of the low 32-bit half of each of the 4 encoding-digest limbs must be zero (2 zero bits per limb × 4 limbs).

## XMSS

`log_lifetime = 32`: a key is valid for up to `2^32` slots. `log_lifetime` corresponds to the Merkle tree height.

## Verification

Inputs: public key `(merkle_root, pp)`, message `msg`, slot `s`, signature `(randomness, chain_tips, merkle_proof)`.

1. **Encode**: compute the 4-limb digest `D = H(H(msg | randomness | tweak_encoding(s)) | pp | 00)`. For each limb `D_i`, take the canonical representative `D_i = low + 2^32 · high` (with `low, high < 2^32`) and reject if `high == 2^32 - 1` (needed for uniformity of the encoding). Reject if the 2 high bits of `low` are non-zero (`encoding_num_final_zeros / 4 = 2` bits per limb). Otherwise split the low 30 bits of `low` into `v / 4 = 10` little-endian chunks of `w = 3` bits each, giving the encoding `(e_0, ..., e_{v-1})` with each `e_i ∈ [0, chain_length)`. Reject if `sum(e_i) ≠ target_sum`.
2. **Recover WOTS public key**: for each `i`, walk chain `i` from `chain_tips[i]` for `chain_length - 1 - e_i` steps, where each step is `H(tweak_chain(i, step, s) | 0 | previous_value | pp | 00)` truncated to `n`.
3. **Hash WOTS public key**: T-sponge with replacement over the `v` recovered chain ends, with IV `[tweak_wots_pk(s) | 0 | pp]`, ingesting two chain end digests at a time. Output is the Merkle leaf.
4. **Walk Merkle path**: for `level = 0..log_lifetime`, combine the current node with `merkle_proof[level]` (left/right determined by bit `level` of `s`) via `H(tweak_merkle(level+1, parent_index) | 0 | pp | left | right)` truncated to `n`.
5. **Check root**: accept iff the final hash equals `merkle_root`.


## Security

target ≈ 128 bits of classical security in the ROM, and ≈ 64 bits of quantum security in the QROM, with an analysis inspired by the section 3.1 of [Tight adaptive reprogramming in the QROM](https://arxiv.org/pdf/2010.15103). TODO write the complete proof.

## Signature size

**1176 bytes** `log2(p).(|randomness| + n.(v + log_lifetime)) / 8`

below IPv6 [MTU](https://fr.wikipedia.org/wiki/Maximum_transmission_unit) (1280 bytes)
