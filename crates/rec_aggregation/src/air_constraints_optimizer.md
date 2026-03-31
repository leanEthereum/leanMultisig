# Optimizing AIR Constraint Code Generation for Recursive Verification

## Problem Statement

When our zkVM verifies a proof recursively, it runs a program (in our zkDSL) that evaluates AIR constraints. This program is **itself proven** — so every operation it performs adds to the cost of the recursive proof.

The AIR constraints are written in Rust using generic types (`PrimeCharacteristicRing`). During compilation to zkDSL, we evaluate them symbolically (`SymbolicExpression<F>`) to produce an expression tree, then convert that tree to zkDSL instructions. The question is: **what zkDSL instructions should we emit for a given constraint expression?**

## The Cost Model

The recursive verification program runs inside our zkVM, which has 3 tables: execution (max 2^25 rows, 20 columns), extension op (max 2^20 rows, 30 columns), and poseidon (max 2^21 rows). The total prover cost is dominated by **table sizes** — each table is padded to the next power of two, then committed via WHIR and verified via sumcheck. Reducing the number of rows in any table reduces proving cost.

### How operations map to table rows

Each zkDSL instruction generates rows in one or more tables:

| Operation | Execution rows | Extension op rows |
|-----------|---------------|-------------------|
| `add_extension_ret(a, b)` | 1 (precompile call) | 1 (add_ee length 1) |
| `mul_extension_ret(a, b)` | 1 | 1 (dot_product_ee length 1) |
| `mul_base_extension_ret(c, a)` | 1 | 1 (dot_product_be length 1) |
| `copy_5(src, dst)` | 5 (5 DEREF instructions) | 0 |
| `dot_product_be(buf, ext, res, N)` | **1** | **N** |
| `dot_product_ee(buf_a, buf_b, res, N)` | **1** | **N** |
| `add_ee(a, b, res, N)` | **1** | **N** |
| `sub_extension_ret(a, b)` | 5 (5 SUB instructions) | 0 |
| `opposite_extension_ret(a)` | 5 | 0 |
| `embed_in_ef(c)` | ~5 | 0 |

**This is the exact cost model — not an approximation.** Each entry comes directly from how the zkDSL compiler translates instructions into VM operations:

- `dot_product_be(N)` compiles to **1 execution-table row** (a single precompile instruction with opcode, operands, and `PRECOMPILE_DATA` encoding the length N and mode) **+ N extension-op-table rows** (one row per element pair processed). This is a hard architectural fact — the precompile instruction occupies 1 row in the execution trace regardless of N, but the extension op table records each inner operation.

- `add_ee(a, b, res, N)` works identically: **1 execution row + N extension op rows**. Same for `dot_product_ee(N)`.

- `copy_5(src, dst)` is an inline function that expands to 5 separate DEREF instructions (not a precompile), hence 5 execution rows and 0 extension op rows.

### Cost analysis

The savings from batching N individual `mul_base_ret + add_ret` into one `dot_product_be(N)`:
- **Execution rows**: (2N-1) → 1. **Saves 2N-2.**
- **Extension op rows**: (2N-1) → N. **Saves N-1.**
- Both tables benefit. This is why batching is "much more efficient."

The cost of making operands contiguous (K copies):
- **Execution rows**: 5K (each copy_5 is 5 DEREF instructions).
- **Extension op rows**: 0.
- Copies are **execution-only** cost. They don't touch the extension op table.

**Both tables matter.** The execution table is larger but cheaper per row (20 columns). The extension op table is smaller but more expensive (30 columns). In the recursive aggregation, both tables are significantly loaded.

## The Constraint: Contiguous Memory

`dot_product_be(base_buf, ext_buf, result, N)` requires:
1. `base_buf`: N contiguous base-field elements (the constants)
2. `ext_buf`: N contiguous extension-field elements (the operands)

The base constants can be **pre-allocated once and reused** (e.g., MDS matrix rows `[2,3,1,1]` used across all rounds). Cost: amortized to ~0.

The extension operands are the problem. They might be:
- **Variables** (column values from `inner_evals`): already contiguous if at consecutive column indices. **Zero-copy** — just pass the pointer.
- **Cached intermediate results**: scattered in memory at various `aux_N` locations. Need `copy_5` per element to make contiguous. **Each copy = 5 execution rows.**
- **Fresh computations**: can be evaluated directly into a pre-allocated contiguous buffer via the `dest` parameter. **Zero extra cost.**

### How `dest` works

`dest` is a **code-generator concept**, not a zkDSL language feature. It controls where expression evaluation results land.

Not every instruction accepts a destination address. The split:

- **Instructions with a built-in destination parameter**: `mul_extension(a, b, dest)`, `add_ee(a, b, dest)`, `sub_extension(a, b, dest)`, `dot_product_be(base, ext, dest, N)`, `dot_product_ee(a, b, dest, N)`. These write their result directly to `dest` — no intermediate allocation, zero extra cost.

- **Instructions without destination** (`_ret` suffix variants): `mul_extension_ret(a, b)`, `add_extension_ret(a, b)`, etc. These allocate a fresh `Array(DIM)` internally and return a pointer. The code generator can't control where the result lands. If a `dest` was requested by the caller, the code generator must emit an additional `copy_5(result, dest)` — adding 5 execution rows.

- **Variables**: Always return `inner_evals + DIM * col_index` (a fixed location). If `dest` was requested, the code generator emits `copy_5(variable, dest)`.

So when evaluating an expression into a buffer slot: if the top-level operation has a dest variant (like `mul_extension` or `dot_product_be`), the result lands directly in the buffer at zero cost. If it doesn't, there's a `copy_5` overhead.

For the internal linear layer `V[i] * state[i] + sum`:
- `V[i] * state[i]` is a `mul_base_extension_ret` → internally `dot_product_be(1)` → **has dest variant**.
- But `+ sum` makes the top-level operation an `add_extension_ret` → **no dest variant** in the `_ret` form, but **`add_ee` does have dest**.

So the code generator needs to use `add_ee(product_result, sum, dest, 1)` instead of `add_extension_ret(product_result, sum)` + `copy_5(result, dest)`. This requires the code generator to prefer dest-supporting variants when a destination is specified.

### How caching and sharing work

Each symbolic expression node has a unique arena index (`u32`). During code generation:

1. **Reference counting**: Before any evaluation, we count how many times each node is referenced across all constraint expressions. Nodes with ref_count > 1 are "shared."
2. **Cache**: A `HashMap<u32, String>` maps arena indices to their zkDSL variable names (e.g., `"aux_42"`). When a shared node is first evaluated, its result is cached. Subsequent references return the cached name.
3. **Evaluation order**: Constraints are evaluated sequentially. The first time a shared sub-expression is encountered, it gets evaluated and cached. Future encounters reuse the cache.

The cached value sits at whatever memory address it was allocated to. There is **no control over this address** — unless `dest` was used during the first evaluation. If a shared node is first evaluated with `dest = state_buf + DIM * 3`, then `"state_buf + DIM * 3"` is what gets cached, and all future references to that sub-expression use that buffer-relative address. **This is key**: by controlling evaluation order and using `dest`, we can force shared values into known contiguous locations.

### Can we control allocation order to get contiguity without `dest`?

**In principle yes, but unreliable.** The zkVM's memory is a write-once array. `Array(N)` allocates the next N words sequentially. So back-to-back `Array(DIM)` calls produce contiguous blocks. But in practice, each element's evaluation creates intermediate values (cube temporaries, partial sums, etc.) that interleave allocations and break contiguity.

The `dest` mechanism with pre-allocated buffers (`Array(DIM * 16)`) is the robust solution.

## The Fundamental Tradeoff

For a weighted sum `c_0 x_0 + c_1 x_1 + ... + c_{N-1} x_{N-1}`:

| Approach | Exec rows | Ext op rows |
|----------|-----------|-------------|
| Individual: N `mul_base_ret` + (N-1) `add_ret` | 2N-1 | 2N-1 |
| `dot_product_be(N)` + K copies (5 exec rows each) | 1 + 5K | N |
| `dot_product_be(N)` + 0 copies (contiguous) | 1 | N |

**Break-even on exec rows**: `1 + 5K < 2N - 1` → `K < (2N-2)/5`.

For N=4: K can be 1 (one copy still saves). K=2 is marginal (11 vs 7). **With contiguous buffer (K=0): saves 6 exec rows + 3 ext op rows per call.**

For N=16: K can be up to 6. **Contiguous: saves 30 exec rows + 15 ext op rows.**

## Where the Opportunities Are

### Poseidon (the biggest target)

The Poseidon table dominates the operation count (~75% of all operations in the recursive verifier). A solution that specifically helps Poseidon is the most impactful. However, the mechanism should be **general-purpose** (reusable for future tables) even if the immediate motivation is Poseidon.

#### External Linear Layer (apply_mat4)
The 4x4 MDS matrix `[[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]` is applied to each group of 4 consecutive state elements. Each output is a weighted sum:

```
output[r] = M[r][0] * state[4g] + M[r][1] * state[4g+1] + M[r][2] * state[4g+2] + M[r][3] * state[4g+3]
```

Applied 9 times per Poseidon evaluation, each time to 4 groups of 4 elements = 16 outputs per layer = **144 total dot_product_be(4) opportunities**.

Constants: 4 reusable arrays `[2,3,1,1]`, `[1,2,3,1]`, `[1,1,2,3]`, `[3,1,1,2]` — written once, used 144 times.

When state is contiguous (buffer or consecutive Variables): cost 1 per output. **Saves 6 exec rows + 3 ext op rows per output.**

#### Internal Linear Layer (20 partial rounds)

Each round: `new_state[i] = V[i] * state[i] + sum` for i=0..15.

- **`sum(state)`**: If state is contiguous, `add_ee(state, state + 8*DIM, result, 8)` = 1 call (1 exec + 8 ext op) vs 15 `add_extension_ret` (15 exec + 15 ext op). **Saves 14 exec + 7 ext op per round.**

- **Individual `new_state[i]`**: 15 independent results. Each is `V[i]*state[i] + sum`. If we write each to a contiguous buffer via `dest`, the next round's operations can use batched instructions. The write is free when using dest-supporting operations.

#### Cross-Group Sums
```
sums[k] = state[k] + state[k+4] + state[k+8] + state[k+12]
```
Stride-4 elements, not contiguous. 3 adds each. Not worth batching (copies would cost more than savings).

### Extension Op Table
Quintic multiplication: sums of 5 ext*ext products. Already detected and optimized.

### Execution Table
Small constraints. Minimal opportunity.

## The Core Strategy: Contiguous Buffer Management

The single biggest optimization is ensuring that **Poseidon state is always in a contiguous 16-element buffer**, so every operation on it can use batched instructions.

### How it would work:

1. **Pre-allocate** `state_buf = Array(DIM * 16)` at the start of each round.
2. **Evaluate** each `new_state[i]` with `dest = state_buf + DIM * i`. For dest-supporting operations, this is free. For others, costs a `copy_5`.
3. **Next round** uses `state_buf` directly for `add_ee(8)`, `dot_product_be(4)`, etc.

### Per partial round savings:

| Operation | Without buffers | With contiguous buffers |
|-----------|----------------|------------------------|
| `sum(state)` | 15 adds (15 exec + 15 ext op) | 1 `add_ee(8)` (1 exec + 8 ext op) |
| `new_state[0] = sum - state[0]` | 1 sub (5 exec) | 1 sub with dest (5 exec) |
| `new_state[1..15]` | 15 mul_base + 15 add (30 exec + 30 ext op) | 15 ops with dest (15 exec + 15 ext op) |
| **Total** | **46 exec + 45 ext op** | **21 exec + 23 ext op** |

Over 20 partial rounds: exec rows 920 → 420, ext op rows 900 → 460. **Saves 500 exec + 440 ext op.**

### Per external linear layer savings:

| Operation | Without buffers | With contiguous buffers |
|-----------|----------------|------------------------|
| mat4 (4 groups x 4 outputs) | 44 adds (44 exec + 44 ext op) | 16 `dot_product_be(4)` (16 exec + 64 ext op) |
| cross-group sums | 12 adds | 12 adds (unchanged) |
| adding sums back | 16 adds | 16 adds (unchanged) |
| **Total** | **72 exec + 72 ext op** | **44 exec + 92 ext op** |

The mat4 optimization **saves exec rows but adds ext op rows** (64 vs 44 = +20 per layer, +180 for 9 layers).

### Current table row counts (AIR eval functions only)

Measured from the generated zkDSL code for all 3 tables:

| Table | Exec rows | Ext op rows |
|-------|-----------|-------------|
| 0 (Execution) | 195 | 69 |
| 1 (Extension Op) | 455 | 212 |
| 2 (Poseidon) | 2,622 | 2,669 |
| **Total** | **3,272** | **2,950** |

**Note**: These are ONLY the AIR constraint evaluation functions. The full recursive verifier program includes much more (sumcheck, WHIR verification, Fiat-Shamir, etc.). These AIR functions are a significant fraction but not the entirety.

For the ext op row concern: the current Poseidon table uses 2,669 ext op rows. Adding 180 (from mat4 dot_product_be) would bring it to ~2,849. The current next-power-of-two boundary is 2^12 = 4,096. So **the +180 does NOT push past a boundary** — there's headroom. The exec row savings (~500) are pure gain.

## Current Implementation

### What exists:
1. **`PREFER_EXPLICIT_MUL`** flag on `PrimeCharacteristicRing`: `false` by default, `true` for `SymbolicExpression`. When true, `apply_mat4` and `internal_layer_mat_mul` use explicit `Const * Var` multiplications instead of the prover's optimized addition trees. The prover is completely unaffected.

2. **`try_emit_dot_product`** with cost check: detects sums of `Mul(Const, Var)` products in the expression tree, batches into `dot_product_be` when cost-effective.

3. **Consecutive Variable detection**: when all operands of a `dot_product_be` are column Variables at consecutive indices, passes the `inner_evals` pointer directly (zero copies).

4. **Constant array caching** (`BE_CONST_CACHE`): base-field constant arrays written once and reused across all matching calls.

### What's missing:
1. **Cost check too strict**: threshold is `copies < N-1`, should account for copy_5 costing 5 exec rows (not 1 ext op row). The correct break-even: `5*copies < 2*(N-1)`. Quick fix.

2. **No contiguous buffer management**: the code generator has no mechanism to pre-allocate a buffer and direct a group of evaluations into it. This is the main missing piece.

3. **No AIR-level grouping hints**: the symbolic expression tree has no concept of "these 16 values form a contiguous state vector." A hint like `assign_to_group` would let the AIR tell the code generator which values to co-locate.

### Does the dest plumbing already work for `V[i]*state[i] + sum`?

**Partially yes.** The code generator (`eval_air_binop`) already selects dest-supporting instruction variants when a `dest` is provided:

- `Add(ext, ext)` with dest → emits `add_ee(a, b, dest)` (1 exec + 1 ext op, writes directly). **Already works.**
- `Mul(const, ext)` with dest → emits `dot_product_be(buf, ext, dest, 1)` (1 exec + 1 ext op, writes directly). **Already works.**
- `Sub(ext, ext)` with dest → emits `sub_extension(a, b, dest)` (1 exec + 1 ext op, writes directly). **Already works.**

So for `V[i]*state[i] + sum`: the top-level operation is `Add(Mul(Const, Var), cached_sum)`. With dest:
1. Inner `Mul(Const, Var)` is evaluated (without dest) → emits `mul_base_extension_ret(V[i], state[i])` → returns a temp.
2. Outer `Add(temp, cached_sum)` with dest → emits `add_ee(temp, cached_sum, dest)` → writes directly to buffer slot.

**Total: 2 ops (1 mul_base_ret + 1 add_ee with dest). No copy_5 needed.** The buffer strategy requires only the buffer allocation logic and the grouping hint — the individual expression-to-instruction translation already handles dest correctly.

What's NOT in place: the mechanism to (a) know that these 16 expressions should go into a contiguous buffer, and (b) trigger their evaluation with the appropriate `dest` values. That's the AIR hint + code-gen support described in Option B.

## Design Options

### Option A: Fix cost check (quick win, ~1 hour)
Change the cost threshold. Enables dot_product_be for all mat4 applications even with scattered operands.

**Expected savings**: ~100 more exec rows for Poseidon.

### Option B: Contiguous buffer management + AIR hints (the big win, ~1-2 days)
Add:
- A new `AirBuilder` method: `assign_to_group(values: &[IF], group_id: &str)` — during symbolic evaluation, records that these N values should be stored contiguously.
- Code-gen support: when a group is declared, pre-allocate `Array(DIM * N)` and evaluate each element with `dest = buffer + DIM * i`.
- Subsequent operations on grouped values detect the contiguous layout and use `dot_product_be`/`add_ee`.

The Poseidon AIR would call this at the end of each round to declare the 16 state elements as a group.

**Expected savings**: 500+ exec rows + 400+ ext op rows for Poseidon.

### Option C: Full 16x16 external layer (extra, on top of B)
Express each output of the full external linear layer as `dot_product_be(16)` using a "doubled state buffer" trick. Saves more exec rows but costs ext op rows.

Worth evaluating after B is implemented.

## Appendix: Operation Counts

### Table 2 (Poseidon) — Original vs Current

| Operation | Original | With `PREFER_EXPLICIT_MUL` |
|-----------|----------|--------------------------|
| `mul_extension_ret` | 297 | 199 |
| `add_extension_ret` | 1291 | 1189 |
| `mul_base_extension_ret` | 181 | 731 |
| `dot_product_be` calls | 0 | 48 |
| `copy_5` | 4 | 4 |
| Unique constant arrays | 0 | 5 |

The `mul_base_extension_ret` increase (181 -> 731) comes from the internal linear layer now using explicit multiplications (via `PREFER_EXPLICIT_MUL`). With contiguous buffer management (Option B), most of these would be written directly into buffers via `dest`, and the subsequent sums would use `add_ee` — dramatically reducing both tables.
