# TODO

## Perf

- WHIR univariate skip
- Opti recursion bytecode
- inverse folding ordering in WHIR to enable Packing during sumcheck (more generally, TODO packing everywhere)
- one can "move out" the variable of the eq(.) polynomials out of the sumcheck computation in WHIR (as done in the PIOP)
- Structured AIR: often no all the columns use both up/down -> only handle the used ones to speed up the PIOP zerocheck
- use RowMAjorMatrix instead of Vec<Vec> for witness, and avoid any transpositions as suggested by Thomas
- Fill Precompile tables during bytecode execution
- Use Univariate Skip to commit to tables with k.2^n rows (k small)
- increase density of multi commitments -> we can almost reduce by 2x commitment costs (question: will perf be good enough in order to avoid using the "jagged pcs" (cf sp1 hypercube)?)
- avoid field embedding in the initial sumcheck of logup*, when table / values are in base field
- opti logup* GKR: 
    - when the indexes are not a power of 2 (which is the case in the execution table)
    - due to padding, the last (potentially up to 50%) part of the pushward is full of 0 -> We can also opti commitment here!
- incremental merkle paths in whir-p3
- Experiment to increase degree, and reduce commitments, in Poseidon arithmetization
- Avoid embedding overhead on the flag, len, and index columns in the AIR table for dot products
- Batched logup*: when computing the eq() factor we can opti if the points contain boolean factor
- Lev's trick to skip some low-level modular reduction
- Sumcheck, case z = 0, no need to fold, only keep first half of the values (done in PR 33 by Lambda) (and also in WHIR?)
- Custom AVX2 / AVX512 / Neon implem in Plonky3 for all of the finite field operations (done for degree 4 extension, but not degree 5)
- the 2 executions of the program, before generating the validity proof, can be merged, using some kind of placeholders
- both WHIR verif + XMSS aggregation programs have 40% of unused memory!! -> TODO improve the compiler to reduce memory fragmentation
- Many times, we evaluate different multilinear polynomials (diferent columns of the same table etc) at a common point. OPTI = compute the eq(.) once, and then dot_product with everything
- To commit to multiple AIR table using 1 single pcs, the most general form our "packed pcs" api should accept is:
 a list of n (n not a power of 2) columns, each ending with m repeated values (in this manner we can reduce proof size when they are a lot of columns (poseidons ...))

## Not Perf

- Whir batching: handle the case where the second polynomial is too small compared to the first one
- bounddary condition on dot_product table: first flag = 1
- verify correctness of the Grand Product check
- Proof size: replace all equality checks in the verifier algo by value deduction
- WIR recursion: batch the multilinear_eval calls on initial merkle leaves
- multilinear_eval precompile: we can reduce the number of sparse equality constraints required to verify the correctness of point / res into the memory

- KoalaBear extension of degree 5: the current implem (in a fork of Plonky3) has not been been optimized
- KoalaBear extension of degree 6: in order to use the (proven) Johnson bound in WHIR

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