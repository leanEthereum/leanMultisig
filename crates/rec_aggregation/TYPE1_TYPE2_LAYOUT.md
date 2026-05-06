# Type-1 / Type-2 public-input layout

**Type-1 — single `(message, slot)` aggregation.** A Type-1 multi-signature attests that *every* public key in a given list signed the **same** `message` at the **same** `slot`. A Type-1 proof can aggregate any mix of (a) raw XMSS signatures verified directly inside the snark, and (b) child Type-1 multi-signatures verified recursively.

**Type-2 — bundle of `n` independent Type-1 multi-signatures.** A Type-2 proof bundles `n` *unrelated* Type-1 multi-signatures into a single snark. Each component may have its own `(message, slot)` and its own pubkey set.

All sizes below are in field elements (FE). One **chunk** = 8 FE. The buffer is hashed chunk-by-chunk with Poseidon (zero IV) to produce the public-input digest.

Worked numbers below assume the bytecode has `log_size = 19` (the current value).

## Flags

| Flag value | Type   | Meaning                               |
| ---------- | ------ | ------------------------------------- |
| `1`        | Type-1 | Single `(message, slot)` aggregation  |
| `0`        | Type-2 | Bundle of `n` Type-1 multi-signatures |

## Common header

| Offset | Size  | Contents                                       |
| ------ | ----- | ---------------------------------------------- |
| `0`    | `8`   | `[flag, count, 0, 0, 0, 0, 0, 0]`              |
| `8`    | `120` | Bytecode evaluation claim (padded up to chunk) |
| `128`  | `8`   | Bytecode-hash domain separator                 |
| `136`  | …     | Component data — layout depends on the flag    |

`count` is `n_sigs` for Type-1, `n_components` for Type-2.

The bytecode-claim region encodes a multilinear evaluation: a point + the resulting value, all over the extension field. Its size is `((log_size + 4 + 1) · 5)` rounded up to a multiple of 8:

- The bytecode is a multilinear polynomial in `log_size + 4` variables. The `+4` comes from `ceil_log2(12)` because each "instruction" occupies 12 columns, padded to 16 = 2⁴ — so addressing one column adds 4 extra variables on top of `log_size`.
- The `+1` adds room for the **value** of the polynomial at that point, alongside the point's coordinates: `(log_size + 4)` coordinates + `1` value = `log_size + 5` extension-field elements.
- The outer `· 5` is the **extension-field degree**: each extension element is 5 base-field elements.
- For `log_size = 19`: `(19 + 4 + 1) · 5 = 24 · 5 = 120` (already a multiple of 8, but otherwise we padd it with zeros).

## Type-1 component data (fixed, 4 chunks = 32 FE)

| Offset | Size | Contents                           |
| ------ | ---- | ---------------------------------- |
| `136`  | `8`  | Hash of all aggregated public keys |
| `144`  | `8`  | Message                            |
| `152`  | `8`  | Merkle chunks identifying the slot |
| `160`  | `8`  | Tweak-table hash                   |

**Total Type-1 buffer = 168 FE = 21 chunks** (independent of `n_sigs`).

## Type-2 component data (variable, `n_components` chunks)

| Offset | Size               | Contents                                                 |
| ------ | ------------------ | -------------------------------------------------------- |
| `136`  | `n_components · 8` | One 8-FE digest per inner Type-1 (its public-input hash) |

**Total Type-2 buffer = `(n_components + 17) · 8` FE**, where `17 = 15` bytecode-claim chunks `+ 1` prefix `+ 1` domsep.

## Picture

```
Type-1 (168 FE):
[flag=1 | n_sigs | 0×6] [bytecode claim, 120 FE] [domsep, 8 FE] [pubkeys_hash | message | merkle_chunks | tweaks_hash]

Type-2 ((n+17)·8 FE):
[flag=0 | n     | 0×6] [bytecode claim, 120 FE] [domsep, 8 FE] [digest_0] [digest_1] … [digest_{n-1}]
```
