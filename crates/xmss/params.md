# XMSS parameters (WIP)

> **Warning:** The current implementation does not match the [leanSig](https://github.com/leanEthereum/leanSig) paper and does not provide 128-bit security in the Standard Model (though it may still be secure in the ROM/QROM). Expect changes in the future.

## 1. Field and Hash

**Field:** KoalaBear, p = 2^31 - 2^24 + 1. Each field element fits in a u32.

**Hash:** Poseidon2 (width 16) in compression mode: `compress: [F; 16] -> [F; 8]`. Applies the Poseidon2 permutation, adds the input (feed-forward), and returns the first 8 elements.

**Digest:** 8 field elements (~248 bits). Used for tree nodes, and chain values.

**Chain step:** `chain_step(x) = compress(x, 0)`. Iterated n times: `iterate_hash(x, n) = chain_step^n(x)`.

## 2. WOTS

| Parameter | Symbol | Value |
|---|---|---|
| Chains | V | 40 |
| Winternitz parameter | W | 3 |
| Chain length | CHAIN_LENGTH | 2^W = 8 |
| Verifier chain hashes | NUM_CHAIN_HASHES | 120 |
| Signer chain hashes | TARGET_SUM | 160 (= V*(CHAIN_LENGTH-1) - NUM_CHAIN_HASHES) |
| Grinding chains | V_GRINDING | 3 |
| Message length | MESSAGE_LEN_FE | 9 |
| Randomness length | RANDOMNESS_LEN_FE | 7 |
| Truncated root length | TRUNCATED_MERKLE_ROOT_LEN_FE | 6 |

### 2.1 Encoding

Converts (message, randomness, slot, truncated_merkle_root) into 40 chain indices via a **fixed-sum encoding** (indices sum to TARGET_SUM, eliminating the need for checksum chains).

1. `A = compress(message[0..8], [message[8], randomness[0..7]])`
2. `B = compress(A, [slot_lo, slot_hi, merkle_root[0..6]])` where slot is split into two 16-bit field elements.
3. Reject if any element of B equals -1 (uniformity guard).
4. Extract 24 bits per element of B (little-endian), split into 3-bit chunks, take first 43.
5. Valid iff: first 40 sum to 160, last 3 all equal 7. Otherwise retry with new randomness.

(Note: adding part of the merkle root to the encoding computation contributes to multi-user security via domain-separation, otherwise the security of the encoding W * (V + V_GRINDING) would degrade bellow 128 bits with multiple users.)

### 2.2 Keys

- **Secret key:** 40 random pre-image digests.
- **Public key:** `pk[i] = iterate_hash(pre_image[i], 7)` for each chain.
- **Public key hash:** sequential left fold: `compress(compress(...compress(pk[0], pk[1])..., pk[38]), pk[39])` (39 compressions).

### 2.3 Sign and Verify

**Sign:** Find randomness r yielding a valid encoding, then `chain_tip[i] = iterate_hash(pre_image[i], encoding[i])`. Signature = (chain_tips, r).

**Verify (public key recovery):** Recompute encoding from (message, slot, truncated_root, r), then `recovered_pk[i] = iterate_hash(chain_tip[i], 7 - encoding[i])`.

## 3. XMSS

**Tree:** Binary Merkle tree of depth LOG_LIFETIME = 32 (2^32 slots). Nodes = `compress(left, right)`.

### 3.1 Key Generation

Inputs: seed (32 bytes), slot range [start, end]. Only WOTS leaves for [start, end] are generated; Merkle nodes outside this range are filled with deterministic random digests (derived from the seed). To an observer, the resulting tree is indistinguishable from a full 2^32-leaf tree.

**Public key:** the Merkle root (single digest).


...
TODO

## 4. Properties

- public key size: 31 bytes
- num. hashes at signing: < 2^16 (mostly grinding at encoding)
- num. hashes at verification: 2 (encoding) + NUM_CHAIN_HASHES + V + LOG_LIFETIME = 194
- sig. size : RANDOMNESS_LEN_FE + 8 * (V + LOG_LIFETIME) = 583 field elements = 2.21 KiB