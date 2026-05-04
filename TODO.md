# TODO

## Perf

- Opti WHIR https://github.com/tcoratger/whir-p3/issues/303 and https://github.com/tcoratger/whir-p3/issues/306 ?
- Avoid the embedding overhead in logup, when denominators = "c - index"
- Fancy zkDSL compiler opti: within each function frame, we could assign one (if any) of the dynamic allocation to the part of the memory coming just after the current frame. This way, the pointer would not be hinted, but rather constant at compile time -> more efficient memory acceses. We could even even have a special keyword (instead of just "Array") to specify which dynamic allocation should benefit from this optimization. Difficulty: that would require to manipulate segments of memory at runtime. Maybe apply this idea to function call and even to loops?
- Further use delayed modular reduction (cf. https://github.com/Plonky3/Plonky3/pull/1592, https://github.com/Plonky3/Plonky3/pull/1597, etc) ?

## Security:

- Fiat Shamir: add a claim tracing feature, to ensure all the claims are indeed checked (Lev)
- Double Check AIR constraints, logup overflows etc
- Do we need to enforce some values at the first row of the dot-product table?
- Formal Verification
- Padd with noop cycles to always ensure memory size >= bytecode size (liveness), and ensure this condition is checked by the verifier (soundness)
- Rewrite the compiler, it's bad right now.

# Ideas

- About range checks, that can currently be done in 3 cycles (see 2.5.3 of the zkVM pdf) + 3 memory cells used. For small ranges we can save 2 memory cells.
- Avoid committing to the 3 index columns, and replace it by a sumcheck? Idea by Georg (Powdr). Advantage: Less commitment surface. Drawback: increase the number of instances in the final WHIR batch opening -> proof size overhead
  
