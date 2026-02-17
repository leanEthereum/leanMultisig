# TODO

## Perf

- 128 bits security
- Merkle pruning
- the interpreter of leanISA (+ witness generation) can be partially parallelized when there are some independent loops
- Make everything "padding aware" (including WHIR, logup, AIR, etc) -> It's hard to remove padding overhead in WHIR at Merkleization, because the FFT "scrambles" the padding, but maybe we can use the fact it's an interleaved RS code ?? TODO explore 
- Opti WHIR: in sumcheck we know more than f(0) + f(1), we know f(0) and f(1)
- Opti WHIR https://github.com/tcoratger/whir-p3/issues/303 and https://github.com/tcoratger/whir-p3/issues/306 ?
- Avoid the embedding overhead in logup, when denominators = "c - index"
- Proof size: replace all equality checks in the verifier algo by value deduction
- Poseidon in 'Compression' mode everywhere (except in 'Sponge' mode? cf. eprint 2014/223)
- Recursion: Remove the few hardcoded constants that depend on the guest execution (cycles etc)
- About the ordering of the variables in sumchecks, currently we do as follows:
- [2024/108](https://eprint.iacr.org/2024/108.pdf) section 3.1
- Fancy zkDSL compiler opti: within each function frame, we could assign one (if any) of the dynamic allocation to the part of the memory coming just after the current frame. This way, the pointer would not be hinted, but rather constant at compile time -> more efficient memory acceses. We could even even have a special keyword (instead of just "Array") to specify which dynamic allocation should benefit from this optimization. Difficulty: that would require to manipulate segments of memory at runtime.

[a, b, c, d, e, f, g, h]                                        (1st round of sumcheck)
[(a-r).a + r.e, (1-r).b + r.f, (1-r).c + r.g, (1-r).d + r.h]    (2nd round of sumcheck)
... etc

This is optimal for packing (SIMD) but not optimal when to comes to padding.
When there are a lot of "ending" zeros, the optimal way of folding is:

[a, b, c, d, e, 0, 0, 0]                                        (1st round of sumcheck)
[(a-r).a + r.b, (1-r).c + r.d, (1-r).e, 0]                      (2nd round of sumcheck)
... etc

But we can get the bost of both worlds (suggested by Lev, TODO implement):

[a, b, c, d, e, f, g, h, i, 0, 0, 0, 0, 0, 0, 0]                                    (1st round of sumcheck)
[(1-r).a + r.c, (1-r).b + r.d, (1-r).e + r.g, (1-r).f + r.h, (1-r).i, 0, 0, 0]      (2nd round of sumcheck)
... etc

## Security:

- Fiat Shamir: add a claim tracing feature, to ensure all the claims are indeed checked (Lev)
- Double Check AIR constraints, logup overflows etc
- Formal Verification
- Padd with noop cycles to always ensure memory size >= bytecode size (liveness), and ensure this condition is checked by the verifier (soundness)

# Ideas

- About range checks, that can currently be done in 3 cycles (see 2.5.3 of the zkVM pdf) + 3 memory cells used. For small ranges we can save 2 memory cells.
- Avoid committing to the 3 index columns, and replace it by a sumcheck? Idea by Georg (Powdr). Advantage: Less commitment surface. Drawback: increase the number of instances in the final WHIR batch opening -> proof size overhead
- Lev's trick to skip some low-level modular reduction?
  
