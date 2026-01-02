# zkDSL Language Reference

## Program Structure

```
import "path/to/file.snark";   // imports (optional)
const NAME = value;            // constants (optional)
fn main() { ... }              // entry point (required)
fn helper() { ... }            // other functions (optional)
```

## Constants

```
const X = 42;
const ARR = [1, 2, 3];
const NESTED = [[1, 2], [3]];
```

### Multi-Dimensional Const Arrays

Const arrays can be nested to any depth, and inner arrays can have different lengths (ragged arrays). All const array values are resolved at compile time.

```
const MATRIX = [[1, 2, 3], [4, 5], [6, 7, 8, 9]];   // ragged 2D array
const DEEP = [[[1, 2], [3]], [[4, 5, 6]]];          // 3D array
```

**Accessing elements:** Use chained indexing with compile-time indices:
```
x = MATRIX[0][2];       // x = 3
y = DEEP[1][0][1];      // y = 5
```

**Using `len()` on inner arrays:** The `len()` function can be applied to any level of a nested const array, including inner arrays accessed by index. This is particularly useful for iterating over ragged arrays where each row has a different length:

```
len(MATRIX)       // 3 
len(MATRIX[0])    // 3 
len(DEEP[0][0])   // 2
```

**Important:** When using `len()` on an inner array with a variable index (e.g., `len(ARR[i])`), the index must be a compile-time constant. This works inside `unroll` loops because the loop variable becomes a compile-time constant during unrolling.

**Example: Iterating over a ragged 2D array:**
```
const MATRIX = [[1, 2, 3], [4, 5], [6, 7, 8, 9]];

fn main() {
    mut total = 0;
    for row in 0..len(MATRIX) unroll {
        for col in 0..len(MATRIX[row]) unroll {
            total = total + MATRIX[row][col];
        }
    }
    assert total == 45;  // 1+2+3+4+5+6+7+8+9
    return;
}
```

## Functions

```
fn add(a, b) -> 1 {           // -> N = return count (omit for 0)
    return a + b;
}

fn swap(a, b) -> 2 {          // multiple return values
    return b, a;
}

fn main() {
    x, y = swap(1, 2);
    return;
}
```

### Parameter Modifiers

| Modifier | Meaning |
|----------|---------|
| (none) | immutable parameter |
| `const` | compile-time value (enables `unroll` with dynamic bounds) |
| `mut` | mutable within function body only |

**All parameters are pass-by-value.** The `mut` modifier allows reassignment within the function, but changes are not visible to the caller. Use return values to communicate results.

```
fn repeat(const n) -> 1 {     // const enables unroll
    mut sum = 0;
    for i in 0..n unroll { sum = sum + i; }
    return sum;
}

fn double(mut x) -> 1 {       // mut allows local reassignment
    x = x * 2;                // only affects local copy
    return x;                 // must return to pass result back
}
```

### Inline Functions
```
fn square(x) inline -> 1 { return x * x; }
```
**Note:** `inline` functions cannot have `mut` parameters.

## Variables

| Declaration | Mutability | Notes |
|-------------|------------|-------|
| `x = 10;` | immutable | cannot be reassigned |
| `mut x = 10;` | mutable | can be reassigned |
| `var x;` | immutable | forward declaration, assign exactly once |
| `var mut x;` | mutable | forward declaration, can be reassigned |

### Forward Declarations

Use `var` when a variable must be assigned in different branches:

```
var result;            // immutable: assign exactly once
if cond == 1 {
    result = 10;
} else {
    result = 20;
}
// result cannot be reassigned after this
```

```
var mut counter;       // mutable: can be reassigned
counter = 0;
counter = counter + 1; // OK
counter = counter + 1; // OK
```

## Memory and Arrays

```
buffer = malloc(16);       // allocate 16 field elements
buffer[0] = 42;
x = buffer[5];

matrix = malloc(64);       // 2D via manual indexing
matrix[row * 8 + col] = value;

ptr2 = ptr + 5;            // pointer arithmetic
ptr2[0] = 100;             // same as ptr[5] = 100
```

**Memory is write-once.** Due to SSA constraints, each memory location can only hold one value. Writing to the same location multiple times is allowed, but all writes must produce the same value—otherwise a runtime error occurs.

```
arr = malloc(3);
arr[0] = 10;               // OK: first write
arr[0] = 10;               // OK: same value
arr[0] = 20;               // ERROR: different value at same location
```

Use `mut` variables (not memory) when you need true mutability.

## Control Flow

### If/Else
```
if x == 0 {
    y = 1;
} else if x == 1 {
    y = 2;
} else {
    y = 3;
}
```
Comparison operators: `==`, `!=`

### Match
Patterns must be consecutive integers starting from 0:
```
match value {
    0 => { result = 100; }
    1 => { result = 200; }
    2 => { result = 300; }
}
```

### For Loops
```
for i in 0..10 { ... }           // standard loop
for i in 0..4 unroll { ... }     // unrolled at compile time
```
Use `unroll` when bounds are const or compile-time expansion is needed.

Loops limitations:
- no "continue" or "break" are supported yet
- the "return" keyword is not supported inside the body of a normal (non-unrolled) loop (because under the hood normal loops are transformed into recursive functions)

## Expressions

### Arithmetic
- `+`, `-`, `*`, `/` (field operations): allowed at runtime
- `%` (modulo), `**` (exponentiation): only allowed at compile time

### Compound Assignment
Syntactic sugar for updating mutable variables:
```
mut x = 10;
x += 5;    // equivalent to: x = x + 5
x -= 3;    // equivalent to: x = x - 3
x *= 2;    // equivalent to: x = x * 2
x /= 4;    // equivalent to: x = x / 4
```

### Built-in Functions
Only allowed at compile time:

```
log2_ceil(x)              // ceiling of log2
next_multiple_of(x, n)    // smallest multiple of n >= x
saturating_sub(a, b)      // max(0, a - b)
len(array)                // length of const array
```

## Assertions

```
// constraint in proof
assert x == y;
assert x != y;
// runtime check only (not constrained by the snark)
debug_assert x == y;
debug_assert x != y;
debug_assert x < y;
```

## Imports

```
import "utils.snark";     // relative to current file
```

## Built-in Constants

```
public_input_start        // pointer to public input
pointer_to_zero_vector    // pre-initialized zeros
pointer_to_one_vector     // [1, 0, 0, ...]
```

## Precompiles

### poseidon16
```
const COMPRESSION = 1;   // (output: 8 elements) (For now this is not a real permutation in the cryptographic sense, see Plonky3 PseudoCompression trait, but it will likely change in the future)
const PERMUTATION = 0;   // full permutation (output: 16 elements)

poseidon16(left, right, output, mode);
```
- `left`, `right`: pointers to 8 field elements each
- `output`: pointer to result (8 or 16 elements depending on mode)
- Used for Merkle tree hashing and Fiat-Shamir:
```
poseidon16(leaf_a, leaf_b, parent_hash, COMPRESSION);  // Merkle node
poseidon16(state, data, new_state, PERMUTATION);       // absorb data
```

### dot_product
```
const DIM = 5;           // extension field degree
const BE = 1;            // base × extension
const EE = 0;            // extension × extension

dot_product(a, b, result, length, mode);
```
- `length`: number of elements in the dot product
- `b`: pointer to `length * DIM` field elements (extension elements)
- `result`: pointer to output (DIM=5 field elements)
- `mode`:
  - `EE`: `a` points to `length * DIM` field elements (extension field elements)
  - `BE`: `a` points to `length` field elements (base field elements)
```
// Multiply two extension field elements (EE mode, length=1)
dot_product(x, y, z, 1, EE);           // z = x * y

// Copy extension element (multiply by [1,0,0,0,0])
dot_product(src, pointer_to_one_vector, dst, 1, EE);
```

## Debugging

```
print(value);
print(a, b, c);
```

## Example

```
const SIZE = 8;

fn main() {
    arr = malloc(SIZE);
    for i in 0..SIZE unroll { arr[i] = i * i; }
    sum = compute_sum(arr, SIZE);
    assert sum == 140;
    return;
}

fn compute_sum(ptr, const n) -> 1 {
    mut acc = 0;
    for i in 0..n unroll { acc = acc + ptr[i]; }
    return acc;
}
```

## Tips

1. Use `unroll` for small, fixed-size loops
2. Use `const` parameters when loop bounds depend on arguments
3. Use `mut` sparingly - immutable is easier to verify
4. Forward declare with `var` (immutable) or `var mut` (mutable) for branch-assigned variables
5. Match patterns must be consecutive from 0 and exhaustive
