# TODO

## Perf

- WHIR univariate skip?
- Opti recursion bytecode
- packing (SIMD) everywhere
- one can "move out" the variable of the eq(.) polynomials out of the sumcheck computation in WHIR (as done in the PIOP)
- Structured AIR: often no all the columns use both up/down -> only handle the used ones to speed up the PIOP zerocheck
- Use Univariate Skip to commit to tables with k.2^n rows (k small)
- opti logup* GKR when the indexes are not a power of 2 (which is the case in the execution table)
- incremental merkle paths in whir-p3
- Avoid embedding overhead on the flag, len, and index columns in the AIR table for dot products
- Lev's trick to skip some low-level modular reduction
- Sumcheck, case z = 0, no need to fold, only keep first half of the values (done in PR 33 by Lambda)
- Custom AVX2 / AVX512 / Neon implem in Plonky3 for all of the finite field operations (done for degree 4 extension, but not degree 5)
- Many times, we evaluate different multilinear polynomials (different columns of the same table etc) at a common point. OPTI = compute the eq(.) once, and then dot_product with everything
- To commit to multiple AIR table using 1 single pcs, the most general form our "packed pcs" api should accept is:
 a list of n (n not a power of 2) columns, each ending with m repeated values (in this manner we can reduce proof size when they are a lot of columns (poseidons ...))
- in the runner of leanISA program, if we call 2 times the same function with the same arguments, we can reuse the same memory frame
- the interpreter of leanISA (+ witness generation) can be partially parallelized when there are some independent loops
- (1 - x).r1 + x.r2 = x.(r2 - r1) + r1 TODO this opti is not everywhere currently + TODO generalize this with the univariate skip
- opti compute_eval_eq when scalar = ONE
- Dmitry's range check, bonus: we can spare 2 memory cells if the value being range check is small (using the zeros present by conventio on the public memory)
- Make everything "padding aware" (including WHIR, logup*, AIR, etc)
- Opti WHIR: in sumcheck we know more than f(0) + f(1), we know f(0) and f(1)
- Opti WHIR https://github.com/tcoratger/whir-p3/issues/303 and https://github.com/tcoratger/whir-p3/issues/306
- Avoid committing to the 3 index columns, and replace it by a sumcheck? Using this idea, we would only commit to PC and FP for the execution table. Idea by Georg (Powdr). Do we even need to commit to FP then?
- Avoid the embedding overhead in logup, when denominators = "c - index", as it was previously done
- SIMD (Packing) for PoW grinding in Fiat-Shamir (has been implemented in the lean-vm-simple branch by [x-senpai-x](https://github.com/x-senpai-x), see [here](https://github.com/leanEthereum/fiat-shamir/blob/d80da40a76c00aaa6d35fe5e51c3bf31eaf8fe17/src/prover.rs#L98))

- About the ordering of the variables in sumchecks, currently we do as follows:

[a, b, c, d, e, f, g, h]                                        (1st round of sumcheck)
[(a-r).a + r.e, (1-r).b + r.f, (1-r).c + r.g, (1-r).d + r.h]    (2nd round of sumcheck)
... etc

This is otpimal for packing (SIMD) but not optimal when to comes to padding.
When there are a lot of "ending" zeros, the optimal way of folding is:

[a, b, c, d, e, 0, 0, 0]                                        (1st round of sumcheck)
[(a-r).a + r.b, (1-r).c + r.d, (1-r).e, 0]                      (2nd round of sumcheck)
... etc

But we can get the bost of both worlds (suggested by Lev, TODO implement):

[a, b, c, d, e, f, g, h, i, 0, 0, 0, 0, 0, 0, 0]                                    (1st round of sumcheck)
[(1-r).a + r.c, (1-r).b + r.d, (1-r).e + r.g, (1-r).f + r.h, (1-r).i, 0, 0, 0]      (2nd round of sumcheck)
... etc

About "the packed pcs" (similar to SP1 Jagged PCS, slightly less efficient, but simpler (no sumchecks)):
- The best strategy is probably to pack as much as possible (the cost increasing the density = additional inner evaluations), if we can fit below a power of 2 - epsilon  (epsilon = 20% for instance, tbd), if the sum of the non zero data is just above a power of 2, no packed technique, even the best, can help us, so we should spread aniway (to reduce the pressure of inner evaluations)
- About those inner evaluations, there is a trick: we need to compute M1(a, b, c, d, ...) then M2(b, c, d, ...), then M3(c, d, ...) -> The trick = compute the "eq(.) for (b, c, d), then dot product with M3. Then expand to eq(b, c, d, ...), dot product with M2. Then expand to eq(a, b, c, d, ...), dot product with M1. The idea is that in this order, computing each "eq" is easier is we start from the previous one.
- Currently the packed pcs works as follows:

```
┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐
| || || || || || || || || || || || || || |
| || || || || || || || || || || || || || |
| || || || || || || || || || || || || || |
| || || || || || || || || || || || || || |
| || || || || || || || || || || || || || |
| || || || || || || || || || || || || || |
└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘
┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐
| || || || || || || || || || || || || || |
| || || || || || || || || || || || || || |
└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘
┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐┌─┐
└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘└─┘
```

But we reduce proof size a lot using instead (TODO):

```
┌────────────────────────┐┌──────────┐┌─┐
|                        ||          || |
|                        ||          || |
|                        ||          || |
|                        ||          || |
|                        ||          || |
|                        ||          || |
└────────────────────────┘└──────────┘└─┘
┌────────────────────────┐┌──────────┐┌─┐
|                        ||          || |
|                        ||          || |
└────────────────────────┘└──────────┘└─┘
┌────────────────────────┐┌──────────┐┌─┐
└────────────────────────┘└──────────┘└─┘
```

## Security:

Fiat Shamir: add a claim tracing feature, to ensure all the claims are indeed checked (Lev)

## Not Perf

- Whir batching: handle the case where the second polynomial is too small compared to the first one
- bounddary condition on dot_product table: first flag = 1
- verify correctness of the Grand Product check
- Proof size: replace all equality checks in the verifier algo by value deduction

- KoalaBear extension of degree 5: the current implem (in a fork of Plonky3) has not been been optimized
- KoalaBear extension of degree 6: in order to use the (proven) Johnson bound in WHIR
- current "packed PCS" is not optimal in the end: can lead to [16][4][2][2] (instead of [16][8])
- make test_packed_pcs pass again
- Poseidon AIR: handle properly the compression mode ? (where output = poseidon(input) + input) (both in WHIR / XMSS)
- XMSS: implem the hash tweak (almost no performance impact as long as we use 1 tweak / XMSS, but this requires further security analysis)
- Grinding before GKR (https://eprint.iacr.org/2025/118)


# Random ideas

- About range checks, that can currently be done in 3 cycles (see 2.5.3 of the zkVM pdf) + 3 memory cells used. For small ranges we can save 2 memory cells.

## Known leanISA compiler bugs:

### Non exhaustive conditions in inlined functions

Currently, to inline functions we simply replace the "return" keyword by some variable assignment, i.e.
we do not properly handle conditions, we would need to add some JUMPs ...

```
fn works(x) inline -> 1 {
    if x == 0 {
        return 0;
    } else {
        return 1;
    }
}

fn doesnt_work(x) inline -> 1 {
    if x == 0 {
        return 0; // will be compiled to `res = 0`;
    } // the bug: we do not JUMP here, when inlined
    return 1; // will be compiled to `res = 1`; -> invalid (res = 0 and = 1 at the same time)
}
```

