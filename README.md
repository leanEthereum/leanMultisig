<h1 align="center">leanMultisig</h1>

<p align="center">
  <img src="./misc/images/banner.svg">
</p>

Minimal hash-based zkVM, targeting recursion and aggregation of hash-based signatures, for a Post-Quantum Ethereum.

Documentation: [PDF](minimal_zkVM.pdf)

## Proving System


- multilinear with [WHIR](https://eprint.iacr.org/2024/1586.pdf), allowing polynomial stacking (reducing proof size)
- [SuperSpartan](https://eprint.iacr.org/2023/552.pdf), with [AIR-specific optimizations](https://solvable.group/posts/super-air/#fnref:1)
- [Logup](https://eprint.iacr.org/2023/1284.pdf), with a system of buses similar to [OpenVM](https://openvm.dev/whitepaper.pdf)

The VM design is inspired by the famous [Cairo paper](https://eprint.iacr.org/2021/1063.pdf).


## Security

123 bits of security. Johnson bound + degree 5 extension of koala-bear -> **no proximity gaps conjecture**. (TODO 128 bits? this would require hash digests bigger than 8 koala-bears).

## Benchmarks (Slightly outdated, new benchmarks incoming)

Machine: M4 Max 48GB (CPU only)

| Benchmark                  | Current              | Target          |
| -------------------------- | -------------------- | --------------- |
| Poseidon2 (16 koala-bears) | `560K Poseidon2 / s` | n/a             |
| 2 -> 1 Recursion           | `1.15 s`             | `0.25 s `       |
| XMSS aggregation           | `554 XMSS / s`       | `1000 XMSS / s` |

*Expect incoming perf improvements.*

To reproduce:
- `cargo run --release -- poseidon --log-n-perms 20`
- `cargo run --release -- recursion --n 2`
- `cargo run --release -- xmss --n-signatures 1300`

## Proof size

WHIR intial rate = 1/4 -> proof size ≈ 225 KiB. (150 KiB with rate 1/16, and < 100 KiB is possible with poximity gaps conjecture + rate 1/16).

(TODO: remaining optimization = [2024/108](https://eprint.iacr.org/2024/108.pdf) section 3.1)

## Credits

- [Plonky3](https://github.com/Plonky3/Plonky3) for its various performant crates
- [whir-p3](https://github.com/tcoratger/whir-p3): a Plonky3-compatible WHIR implementation
- [Whirlaway](https://github.com/TomWambsgans/Whirlaway): Multilinear snark for AIR + minimal zkVM


