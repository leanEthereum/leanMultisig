<h1 align="center">leanMultisig</h1>

<p align="center">
  <img src="./misc/images/banner.svg">
</p>

Minimal hash-based zkVM, targeting recursion and aggregation of hash-based signatures, for a Post-Quantum Ethereum.

Documentation: [PDF](minimal_zkVM.pdf)

## Proving System


- multilinear with [WHIR](https://eprint.iacr.org/2024/1586.pdf)
- [SuperSpartan](https://eprint.iacr.org/2023/552.pdf), with [AIR-specific optimizations](https://solvable.group/posts/super-air/#fnref:1)
- [Logup](https://eprint.iacr.org/2023/1284.pdf) / [Logup*](https://eprint.iacr.org/2025/946.pdf)

The VM design is inspired by the famous [Cairo paper](https://eprint.iacr.org/2021/1063.pdf).


## Security

123 bits of security. Johnson bound + degree 5 extension of koala-bear -> **no proximity gaps conjecture**. (TODO 128 bits, which requires hash digests bigger than 8 koala-bears).

## Benchmarks

Machine: M4 Max 48GB (CPU only)

| Benchmark                  | Current              | Target          |
| -------------------------- | -------------------- | --------------- |
| Poseidon2 (16 koala-bears) | `560K Poseidon2 / s` | n/a             |
| 2 -> 1 Recursion           | `1.35 s`             | `0.25 s `       |
| XMSS aggregation           | `554 XMSS / s`       | `1000 XMSS / s` |

*Expect incoming perf improvements.*

To reproduce:
- `cargo run --release -- poseidon --log-n-perms 20`
- `cargo run --release -- recursion --n 2`
- `cargo run --release -- xmss --n-signatures 1350`

(Small detail remaining in recursion: final (multilinear) evaluation of the guest program bytecode, there are multiple ways of handling it... TBD soon)

## Proof size

WHIR intial rate = 1/4. Proof size ≈ 325 KiB. TODO: WHIR batch opening + [2024/108](https://eprint.iacr.org/2024/108.pdf) section 3.1  -> close to 256 KiB. (To go below 256 KiB -> rate 1/8 or 1/16 in the final recursion).

## Credits

- [Plonky3](https://github.com/Plonky3/Plonky3) for its various performant crates
- [whir-p3](https://github.com/tcoratger/whir-p3): a Plonky3-compatible WHIR implementation
- [Whirlaway](https://github.com/TomWambsgans/Whirlaway): Multilinear snark for AIR + minimal zkVM


