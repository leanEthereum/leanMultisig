# TODO

## Perf

- WHIR univariate skip?
- Opti recursion bytecode
- inverse folding ordering in WHIR to enable Packing during sumcheck (more generally, TODO packing everywhere)
- one can "move out" the variable of the eq(.) polynomials out of the sumcheck computation in WHIR (as done in the PIOP)
- Structured AIR: often no all the columns use both up/down -> only handle the used ones to speed up the PIOP zerocheck
- avoid transpositions (poseidon trace generation)
- Use Univariate Skip to commit to tables with k.2^n rows (k small)
- avoid field embedding in the initial sumcheck of logup*, when table / values are in base field
- opti logup* GKR when the indexes are not a power of 2 (which is the case in the execution table)
- incremental merkle paths in whir-p3
- Experiment to increase degree, and reduce commitments, in Poseidon arithmetization. 
  Result: degree 9 is better than 3. TODO: degree 5, or 6 ? Also, the current degre 9 implem may not be perfectly optimal?
- Avoid embedding overhead on the flag, len, and index columns in the AIR table for dot products
- Batched logup*: when computing the eq() factor we can opti if the points contain boolean factor
- Lev's trick to skip some low-level modular reduction
- Sumcheck, case z = 0, no need to fold, only keep first half of the values (done in PR 33 by Lambda) (and also in WHIR?)
- Custom AVX2 / AVX512 / Neon implem in Plonky3 for all of the finite field operations (done for degree 4 extension, but not degree 5)
- Many times, we evaluate different multilinear polynomials (different columns of the same table etc) at a common point. OPTI = compute the eq(.) once, and then dot_product with everything
- To commit to multiple AIR table using 1 single pcs, the most general form our "packed pcs" api should accept is:
 a list of n (n not a power of 2) columns, each ending with m repeated values (in this manner we can reduce proof size when they are a lot of columns (poseidons ...))
- in the runner of leanISA program, if we call 2 times the same function with the same arguments, we can reuse the same memory frame
- the interpreter of leanISA (+ witness generation) can be partially parallelized when there are some independent loops
- (1 - x).r1 + x.r2 = x.(r2 - r1) + r1 TODO this opti is not everywhere currently + TODO generalize this with the univaraite skip
- opti compute_eval_eq when scalar = ONE
- Dmitry's range check, bonus: we can spare 2 memory cells if the value being range check is small (using the zeros present by conventio on the public memory)
- Make everything "padding aware" (including WHIR, logup*, AIR, etc)
- Opti WHIR: in sumcheck we know more than f(0) + f(1), we know f(0) and f(1)
- Opti WHIR https://github.com/tcoratger/whir-p3/issues/303 and https://github.com/tcoratger/whir-p3/issues/306
- Avoid committing to extra columns / adding some constraints in poseidon16 AIR, for "compression", and use instead sumcheck

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

## Not Perf

- Whir batching: handle the case where the second polynomial is too small compared to the first one
- bounddary condition on dot_product table: first flag = 1
- verify correctness of the Grand Product check
- Proof size: replace all equality checks in the verifier algo by value deduction
- WIR recursion: batch the multilinear_eval calls on initial merkle leaves
- multilinear_eval precompile: we can reduce the number of sparse equality constraints required to verify the correctness of point / res into the memory

- KoalaBear extension of degree 5: the current implem (in a fork of Plonky3) has not been been optimized
- KoalaBear extension of degree 6: in order to use the (proven) Johnson bound in WHIR
- current "packed PCS" is not optimal in the end: can lead to [16][4][2][2] (instead of [16][8])
- make test_packed_pcs pass again
- Poseidon AIR: handle properly the compression mode ? (where output = poseidon(input) + input) (both in WHIR / XMSS)
- XMSS: implem the hash tweak (almost no performance impact as long as we use 1 tweak / XMSS, but this requires further security analysis)


# Random ideas

- About range checks, that can currently be done in 3 cycles (see 2.5.3 of the zkVM pdf), in the instruction encoding of DEREF, if we replaced (1 - AUX) by a dedicated column,
  we could allow DEREFS that 'does not do anything with the resulting value', which is exactly what we want for range check: we only want to ensure that m[m[fp + x]] (resp m[(t-1) - m[fp + x]])
  is a valid memory access (i.e. the index is < M the memory size), but currently the DEREF instruction forces us to 'store' the result, in m[fp + i] (resp m[fp + k]).
  TLDR: adding a new encoding field for DEREF would save 2 memory cells / range check. If this can also increase perf in alternative scenario (other instructions for instance),
  potentially we should consider it.

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

