# XMSS parameters

> **Warning:** The current implementation does not match the [leanSig](https://github.com/leanEthereum/leanSig) paper and does not provide 128-bit security in the Standard Model (though it may still be secure in the ROM/QROM). Expect changes in the future.

## 1. Field and Hash

**Field:** KoalaBear, p = 2^31 - 2^24 + 1. Each field element fits in a u32.

**Hash:** Poseidon1 (width 24) in compression mode: `compress: [F; 24] -> [F; 9]` (capacity 9, rate 15). Applies the Poseidon1 permutation, adds the input (feed-forward), and returns the first 9 elements.

**Digest:** 8 field elements (~248 bits). Used for tree nodes and chain values (taken from first 8 of the 9-element output).

**Public parameter:** 5 field elements, derived deterministically from the seed.

**Tweaks:** 2 field elements for domain separation. Encodes (tweak_type, sub_position, index) where tweak_type distinguishes chain/wots_pk/merkle/encoding operations.

**Chain step:** `chain_step(x, tweak, pp) = compress(zeros(9) || x(8) || tweak(2) || pp(5))[0..8]`. Iterated n times with per-step tweaks.

## 2. WOTS

| Parameter | Symbol | Value |
|---|---|---|
| Chains | V | 45 |
| Winternitz parameter | W | 3 |
| Chain length | CHAIN_LENGTH | 2^W = 8 |
| Verifier chain hashes | NUM_CHAIN_HASHES | 115 |
| Signer chain hashes | TARGET_SUM | 200 (= V*(CHAIN_LENGTH-1) - NUM_CHAIN_HASHES) |
| Message length | MESSAGE_LEN_FE | 9 |
| Randomness length | RANDOMNESS_LEN_FE | 7 |
| Public parameter length | PUBLIC_PARAM_LEN_FE | 5 |
| Tweak length | TWEAK_LEN | 2 |
| Secret size (per chain) | DIGEST_SIZE | 8 |

### 2.1 Encoding

Converts (message, slot, public_param, randomness) into 45 chain indices via a **fixed-sum encoding** (indices sum to TARGET_SUM, eliminating the need for checksum chains).

1. `compressed = Poseidon1_24_compress(message(9) || tweak(2) || randomness(7) || public_param(5) || 0)`
2. Reject if any element of compressed equals -1 (uniformity guard).
3. Extract 15 bits per element (little-endian), split into 3-bit chunks: 9 elements * 5 values = 45 values.
4. Valid iff: all 45 values sum to 200. Otherwise retry with new randomness.

Domain separation via public_param ensures multi-user security without needing grinding chains.

### 2.2 Keys

- **Secret key:** 45 random pre-image digests (8 FE each).
- **Public key:** `pk[i] = iterate_hash(pre_image[i], 7, pp, slot, i, 0)` for each chain.
- **Public key hash:** sequential Poseidon24 sponge: for each chain i, `capacity = compress(capacity(9) || pk[i](8) || tweak(2) || pp(5))` (45 compressions). Output = capacity[0..8].

### 2.3 Sign and Verify

**Sign:** Find randomness r yielding a valid encoding, then `chain_tip[i] = iterate_hash(pre_image[i], encoding[i], pp, slot, i, 0)`. Signature = (chain_tips, r).

**Verify (public key recovery):** Recompute encoding from (message, slot, public_param, r), then `recovered_pk[i] = iterate_hash(chain_tip[i], 7 - encoding[i], pp, slot, i, encoding[i])`.

## 3. XMSS

**Tree:** Binary Merkle tree of depth LOG_LIFETIME = 32 (2^32 slots). Nodes = `Poseidon1_24_compress(left(8) || right(8) || tweak(2) || public_param(5) || 0)[0..8]`.

### 3.1 Key Generation

Inputs: seed (20 bytes), slot range [start, end]. Only WOTS leaves for [start, end] are generated; Merkle nodes outside this range are filled with deterministic random digests (derived from the seed). Public parameter derived deterministically from seed (domain separator 0x02).

**Public key:** Merkle root (8 FE) + public parameter (5 FE) = 13 field elements.

## 4. Properties

- public key size: 13 field elements = ~50 bytes
- num. hashes at signing: < 2^16 (mostly grinding at encoding)
- num. hashes at verification: 1 (encoding) + NUM_CHAIN_HASHES + V (WOTS PK hash) + LOG_LIFETIME (Merkle) = 1 + 115 + 45 + 32 = 193
- sig. size: RANDOMNESS_LEN_FE + 8 * (V + LOG_LIFETIME) = 7 + 8 * 77 = 623 field elements = 2.43 KiB
