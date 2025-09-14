<h1 align="center">♦ leanMultisig ♦</h1>

XMSS + minimal [zkVM](minimal_zkVM.pdf) = lightweight PQ signatures, with unbounded aggregation


## Proving System


- AIR tables committed via multilinear polynomial, using [WHIR](https://eprint.iacr.org/2024/1586.pdf)
- [SuperSpartan](https://eprint.iacr.org/2023/552.pdf), with AIR-specific optimizations developed by W. Borgeaud in [A simple multivariate AIR argument inspired by SuperSpartan](https://solvable.group/posts/super-air/#fnref:1)
- [Univariate Skip](https://eprint.iacr.org/2024/108.pdf)
- [Logup*](https://eprint.iacr.org/2025/946.pdf)
- ...

The VM design is inspired by the famous [Cairo paper](https://eprint.iacr.org/2021/1063.pdf).

Details on how to prove AIR constraints in the multilinear settings are described in [Whirlaway.pdf](Whirlaway.pdf).


## Benchmarks

cpu: cpu: i9-12900H, ram: 32 gb

> TLDR: Slow, **but there is hope** (cf [TODO](TODO.md))

target ≈ 128 bits of security, currently using conjecture: 4.12 of [WHIR](https://eprint.iacr.org/2024/1586.pdf), "up to capacity" (TODO: a version without any conjecture, requires an extension of koala-bear of degree > 5)

### Poseidon2

```console
RUSTFLAGS='-C target-cpu=native' cargo run --release
```

50 % over 16 field elements, 50 % over 24 field elements. rate = 1/2

![Alt text](docs/benchmark_graphs/graphs/raw_poseidons.svg)

### Recursion

```console
RUSTFLAGS='-C target-cpu=native' cargo test --release --package rec_aggregation --lib -- recursion::test_whir_recursion --nocapture
```

The full recursion program is not finished yet. Instead, we prove validity of a WHIR opening, with 25 variables, and rate = 1/4.

![Alt text](docs/benchmark_graphs/graphs/recursive_whir_opening.svg)

### XMSS aggregation

```console
RUSTFLAGS='-C target-cpu=native' NUM_XMSS_AGGREGATED='500' cargo test --release --package rec_aggregation --lib -- xmss_aggregate::test_xmss_aggregate --nocapture
```

500 XMSS aggregated. "Trivial encoding" (for now).

![Alt text](docs/benchmark_graphs/graphs/xmss_aggregated_time.svg)
![Alt text](docs/benchmark_graphs/graphs/xmss_aggregated_overhead.svg)

### Proof size

With conjecture "up to capacity", current proofs with rate = 1/2 are about about ≈ 400 - 500 KiB, in which ≈ 300 KiB comes from WHIR.

- The remaining 100 - 200 KiB will be significantly reduced in the future (this part has not been optimized at all).
- WHIR proof size will also be reduced, thanks to merkle pruning (TODO).

Reasonable target: 256 KiB for fast proof, 128 KiB for slower proofs (rate = 1/4 or 1/8).

## Credits

- [Plonky3](https://github.com/Plonky3/Plonky3) for its various performant crates (Finite fields, poseidon2 AIR etc)
- [whir-p3](https://github.com/tcoratger/whir-p3): a Plonky3-compatible WHIR implementation
- [Whirlaway](https://github.com/TomWambsgans/Whirlaway): Multilinear snark for AIR + minimal zkVM


