# zkDSL Language Reference

## Program Structure

```
from snark_lib import *        # Python compatibility (ignored by compiler)
from dir.file import *         # imports (optional, Python-style)
NAME = value                   # constants (optional, uppercase by convention)
def main():                     # entry point (required)
    ...
def helper():                   # other functions (optional)
    ...
```

The `from snark_lib import *` line imports Python definitions for zkDSL primitives (Array, DynArray, Mut, Const, etc.), allowing `.py` files to be executed as normal Python scripts for testing. The zkDSL compiler ignores this import line.

To run zkDSL files as Python scripts, run from the file's directory with PYTHONPATH pointing to the lean_compiler crate (for snark_lib.py):
```bash
export PYTHONPATH=/path/to/repo/crates/lean_compiler
cd crates/lean_compiler/tests/test_data
python program_0.py
```

## Constants

Constants are declared at the top level (outside functions) using simple assignment. By convention, constant names are UPPERCASE.

```
X = 42
ARR = [1, 2, 3]
NESTED = [[1, 2], [3]]
```

### Multi-Dimensional Const Arrays

Const arrays can be nested to any depth, and inner arrays can have different lengths (ragged arrays). All const array values are resolved at compile time.

```
MATRIX = [[1, 2, 3], [4, 5], [6, 7, 8, 9]]   # ragged 2D array
DEEP = [[[1, 2], [3]], [[4, 5, 6]]]          # 3D array
```

**Accessing elements:** Use chained indexing with compile-time indices:
```
x = MATRIX[0][2]       # x = 3
y = DEEP[1][0][1]      # y = 5
```

**Using `len()` on inner arrays:** The `len()` function can be applied to any level of a nested const array, including inner arrays accessed by index. This is particularly useful for iterating over ragged arrays where each row has a different length:

```
len(MATRIX)       # 3
len(MATRIX[0])    # 3
len(DEEP[0][0])   # 2
```

**Important:** When using `len()` on an inner array with a variable index (e.g., `len(ARR[i])`), the index must be a compile-time constant. This works inside `unroll` loops because the loop variable becomes a compile-time constant during unrolling.

**Example: Iterating over a ragged 2D array:**
```
MATRIX = [[1, 2, 3], [4, 5], [6, 7, 8, 9]]

def main():
    total: Mut = 0
    for row in unroll(0, len(MATRIX)):
        for col in unroll(0, len(MATRIX[row])):
            total = total + MATRIX[row][col]
    assert total == 45  # 1+2+3+4+5+6+7+8+9
    return
```

## Functions

```
def add(a, b):                # return count is inferred from return statements
    return a + b

def swap(a, b):               # multiple return values
    return b, a

def main():
    x, y = swap(1, 2)
    return
```

The number of return values is automatically inferred from the `return` statements. All return statements in a function must return the same number of values.

### Parameter Modifiers

| Syntax | Meaning |
|--------|---------|
| `x` | immutable parameter |
| `x: Const` | compile-time value (enables `unroll` with dynamic bounds) |
| `x: Mut` | mutable within function body only |

**All parameters are pass-by-value.** The `: Mut` modifier allows reassignment within the function, but changes are not visible to the caller. Use return values to communicate results.

```
def repeat(n: Const):         # Const enables unroll
    sum: Mut = 0
    for i in unroll(0, n):
        sum = sum + i
    return sum

def double(x: Mut):           # Mut allows local reassignment
    x = x * 2                # only affects local copy
    return x                 # must return to pass result back
```

### Inline Functions
Use the `@inline` decorator to mark functions for inlining at call sites:
```
@inline
def square(x):
    return x * x
```
**Note:** Inline functions cannot have `: Mut` parameters.

## Variables

| Declaration | Mutability | Notes |
|-------------|------------|-------|
| `x = 10` | immutable | cannot be reassigned |
| `x: Mut = 10` | mutable | can be reassigned |
| `x: Imu` | immutable | forward declaration, assign exactly once later |
| `x: Mut` | mutable | forward declaration for mutable variable |

### Forward Declarations

Use `x: Imu` when a variable must be assigned in different branches:

```
result: Imu            # immutable: assign exactly once
if cond == 1:
    result = 10
else:
    result = 20
# result cannot be reassigned after this
```

Use `x: Mut` when you need the variable to be mutable after assignment:

```
x: Mut
if cond == 1:
    x = 10
else:
    x = 20
x = x + 1            # OK: x was declared as mutable
```

### Tuple Assignments with Mutable Variables

When a function returns multiple values and some need to be mutable, use forward declarations:

```
b: Mut                # declare b as mutable
a, b, c = some_function()
# a and c are immutable, b is mutable
b = b + 1  # OK
# a = 5   # ERROR: a is immutable
```

This is useful when a function returns multiple values and only some need to be modified later.

## Memory and Arrays

```
buffer = Array(16)       # allocate 16 field elements
buffer[0] = 42
x = buffer[5]

matrix = Array(64)       # 2D via manual indexing
matrix[row * 8 + col] = value

ptr2 = ptr + 5            # pointer arithmetic
ptr2[0] = 100             # same as ptr[5] = 100
```

**Memory is write-once.** Due to SSA constraints, each memory location can only hold one value. Writing to the same location multiple times is allowed, but all writes must produce the same value—otherwise a runtime error occurs.

```
arr = Array(3)
arr[0] = 10               # OK: first write
arr[0] = 10               # OK: same value
arr[0] = 20               # ERROR: different value at same location
```

Use `mut` variables when you need mutability, the compiler cannot handle mutability on hand-written allocated memory ("Array(...)").

## DynArray (Compile-Time Dynamic Arrays)

DynArrays are compile-time constructs for building dynamic arrays. Unlike `Array`, DynArrays track structure at compile time—each element gets its own memory slot.

```
v = DynArray([1, 2, 3])  # create dynamic array
v.push(4)                # append element
v.pop()                  # remove last element (does not return it)
x = v[2]                 # access (index must be compile-time constant)
n = len(v)               # get length
```

### Nested DynArrays

```
matrix = DynArray([DynArray([1, 2]), DynArray([3, 4, 5])])
matrix[1].push(6)        # push to inner array
matrix[0].pop()          # pop from inner array
x = matrix[0][0]         # x = 1
n = len(matrix[1])       # n = 4
```

### Building DynArrays in Loops

Use `unroll` loops to build arrays dynamically:

```
v = DynArray([])
for i in unroll(0, 5):
    v.push(i * i)        # v = [0, 1, 4, 9, 16]
```

### Restrictions

DynArrays are compile-time only. The compiler must know the exact structure at every point:

1. **Indices must be compile-time constants** (literals or unroll loop variables)
2. **Push/pop to outer-scope arrays forbidden** inside `if/else`, `match`, or non-unrolled loops
3. **DynArrays cannot be passed to non-inlined functions**
4. **Pop on empty array is a compile error**

```
# OK: local array in branch
if cond == 1:
    v = DynArray([1, 2])
    v.push(3)

# ERROR: push to outer-scope array in branch
v = DynArray([1, 2])
if cond == 1:
    v.push(3)            # compile error

# OK: same variable name in different branches
if cond == 1:
    v = DynArray([1])
else:
    v = DynArray([2, 3]) # different structure, but only one executes
```

## Control Flow

### If/Else
```
if x == 0:
    y = 1
elif x == 1:
    y = 2
else:
    y = 3
```
Comparison operators: `==`, `!=`

### Match
Patterns must be consecutive integers:
```
match value:
    case 5:
        result = 500
    case 6:
        result = 600
    case 7:
        result = 700
```

### match_range

Compile-time construct that expands into a match statement, useful for dispatching to functions with const parameters based on runtime values. Results are always immutable.

```
result = match_range(n, range(1, 5), lambda i: compute(i))
```
Expands to:
```
result: Imu  # auto-generated forward declaration (always immutable)
match n:
    case 1: result = compute(1)
    case 2: result = compute(2)
    case 3: result = compute(3)
    case 4: result = compute(4)
```

**Multiple continuous ranges** with different lambdas:
```
result = match_range(n,
    range(0, 1), lambda i: special_case(),
    range(1, 8), lambda i: normal_case(i))
```
Expands to a match where case 0 uses `special_case()` and cases 1-7 use `normal_case(i)`.

Ranges must be continuous (end of one equals start of next).

**Multiple return values:**
```
a, b = match_range(n, range(0, 4), lambda i: two_values(i))
```

**Common use case:** Dispatching runtime values to const-parameter functions:
```
def helper_const(n: Const):
    # function that requires compile-time n
    return n * n

def compute(value):
    result = match_range(value, range(0, 10), lambda i: helper_const(i))
    return result
```

**IMPORTANT:** For both `match` and `match_range`, the programmer must ensure the value is within the specified range. Out-of-range values cause undefined behavior. Use `debug_assert` to validate:
```
debug_assert(n < 10)
debug_assert(0 < n)
result = match_range(n, range(1, 10), lambda i: compute(i))
```

### For Loops
```
for i in range(0, 10):                  # standard loop
    ...
for i in unroll(0, 4):                  # unrolled at compile time
    ...
for i in dynamic_unroll(5, a, n_bits):  # a must be compile-time known, and a < 2^n_bits
    ...
```
Use `unroll` when bounds are const or compile-time expansion is needed.

**`dynamic_unroll`** enables iterating from `start` to a runtime value `a` (where `a - start` is known to be < 2^n_bits) in an unrolled fashion. The compiler automatically generates bit decomposition of `a - start`, verification constraints, and conditional execution for each index. Both `start` and `n_bits` must be compile-time known.

**Mutable variables in non-unrolled loops:** Mutable variables can be modified inside non-unrolled loops. The compiler automatically transforms these into buffer-based implementations:

```
sum: Mut = 0
for i in range(1, 11):
    sum += i
assert sum == 55
```

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
x: Mut = 10
x += 5    # equivalent to: x = x + 5
x -= 3    # equivalent to: x = x - 3
x *= 2    # equivalent to: x = x * 2
x /= 4    # equivalent to: x = x / 4
```

### Built-in Functions
Only allowed at compile time:

```
log2_ceil(x)              # ceiling of log2
next_multiple_of(x, n)    # smallest multiple of n >= x
saturating_sub(a, b)      # max(0, a - b)
len(array)                # length of const array or vector
```

## Assertions

```
# constraint in proof
assert x == y
assert x != y
# unconditional failure (panic)
assert False
assert False, "error message"
# runtime check only (not constrained by the snark)
debug_assert(x == y)
debug_assert(x != y)
debug_assert(x < y)
```

## Comments

```
# Single-line comment

"""
Multi-line comment
can span multiple lines
"""
```

## Imports

```
from utils import *          # imports utils.py (relative to import root)
from dir.subdir.file import *  # imports dir/subdir/file.py
```

## Built-in Constants

```
NONRESERVED_PROGRAM_INPUT_START        # pointer to public input
ZERO_VEC_PTR    # pre-initialized zeros
ONE_EF_PTR     # [1, 0, 0, ...]
```

## Precompiles

### poseidon16
Always in "compression" mode
```
poseidon16(left, right, output, mode)
```
- `left`, `right`: pointers to 8 field elements each
- `output`: pointer to result (8 elements)
```
poseidon16(leaf_a, leaf_b, parent_hash)
poseidon16(state, data, new_state)
```

### Extension Operations

Six built-in functions route through a single `extension_op` precompile table. Each combines an element-wise operation with an accumulation over `length` element pairs.

```
func(ptr_a, ptr_b, ptr_result)            # length defaults to 1
func(ptr_a, ptr_b, ptr_result, length)    # explicit length (N elements)
```

**Operand types (suffix):**
- `_ee`: both `ptr_a` and `ptr_b` point to extension field elements (5 consecutive field elements each, stride = DIM)
- `_be`: `ptr_a` points to base field elements (stride 1), `ptr_b` points to extension field elements (stride DIM)

`ptr_result` always points to a single extension field element (DIM=5 field elements).

**Operations:**

| Function | Element-wise | Accumulation |
|----------|-------------|--------------|
| `add_ee` / `add_be` | `e_i = a_i + b_i` | `result = sum(e_i)` |
| `dot_product_ee` / `dot_product_be` | `e_i = a_i * b_i` | `result = sum(e_i)` |
| `poly_eq_ee` / `poly_eq_be` | `e_i = a_i*b_i + (1-a_i)*(1-b_i)` | `result = prod(e_i)` |

**Note:** `length` must be a compile-time constant. For runtime-known lengths, use `match_range` to dispatch (see example below).

```
# Multiply two extension field elements (length=1, default)
dot_product_ee(x, y, z)              # z = x * y

# Copy extension element (multiply by [1,0,0,0,0])
dot_product_ee(src, ONE_EF_PTR, dst)

# Dot product of N extension field elements
dot_product_ee(coeffs, basis, result, N)

# Dot product with base-field scalars
dot_product_be(alpha_powers, coeffs, result, N)

# Extension field addition: c = a + b
add_ee(a, b, c)

# Extension field subtraction via constraint: c = a - b  <=>  b + c = a
add_ee(b, c, a)

# Equality polynomial: eq(a, b) = a*b + (1-a)*(1-b)
poly_eq_ee(a, b, eq_result)

# Multi-point equality polynomial: prod_{i=0}^{n-1} eq(a[i], b[i])
poly_eq_ee(a, b, result, n)

# Runtime-known length via match_range
def dot_product_ee_dynamic(a, b, res, n):
    debug_assert(n <= 256)
    match_range(n, range(1, 257), lambda i: dot_product_ee(a, b, res, i))
```

## Debugging

```
print(value)
print(a, b, c)
```

## Example

```
SIZE = 8

def main():
    arr = Array(SIZE)
    for i in unroll(0, SIZE):
        arr[i] = i * i
    sum = compute_sum(arr, SIZE)
    assert sum == 140
    return

def compute_sum(ptr, n: Const):
    acc: Mut = 0
    for i in unroll(0, n):
        acc = acc + ptr[i]
    return acc
```

## Line Continuation

Like Python, lines can be continued in two ways:

### Implicit continuation (inside parentheses/brackets/braces)

Expressions inside `()`, `[]`, or `{}` can span multiple lines without any special syntax:

```
result = function_call(
    arg1,
    arg2,
    arg3
)

arr = DynArray([
    1,
    2,
    3
])
```

### Explicit continuation with backslash

Long lines can also be split using `\` at the end of a line:

```
x = very_long_function_name(arg1, \
    arg2, \
    arg3)

y = 1 + 2 + \
    3 + 4
```

The `\` and following newline are replaced with a single space. Any whitespace after `\` and before the newline is ignored.

## Tips

1. Use `unroll` for small, fixed-size loops
2. Use `const` parameters when loop bounds depend on arguments
3. Use `mut` sparingly - immutable is easier to verify
4. Use `x: Imu` or `x: Mut` for forward-declaring variables that will be assigned in branches
5. Match patterns must be consecutive integers (can start from any value)

## Example: From high level syntactic sugar to minimal ISA, with read-only memory

Take the following program:

```
def main():
    x: Mut = 0
    y: Mut = 3
    x += y
    y += x
    for i in range(4, 6):
        x += i
        x += y
        y = i
        y += x
    assert x == 35
    assert y == 40
    return
```

First, we use buffers to handle mutable variables across (non-unrolled) loops.

```
def main():
    x: Mut = 0
    y: Mut = 3
    x += y
    y += x
    size = 6 - 4
    x_buff = Array(size + 1)
    x_buff[0] = x
    y_buff = Array(size + 1)
    y_buff[0] = y
    for i in range(4, 6):
        buff_idx = i - 4
        x_body: Mut = x_buff[buff_idx]
        y_body: Mut = y_buff[buff_idx]
        x_body += i
        x_body += y_body
        y_body = i
        y_body += x_body
        next_idx = buff_idx + 1
        x_buff[next_idx] = x_body
        y_buff[next_idx] = y_body
    x = x_buff[size]
    y = y_buff[size]
    assert x == 35
    assert y == 40
    return
```

Then, use auxiliary variables to transform it into SSA form (Static Single-Assignment):


```
def main():
    x = 0
    y = 3
    x2 = x + y
    y2 = y + x2
    size = 6 - 4
    x_buff = Array(size + 1)
    x_buff[0] = x2
    y_buff = Array(size + 1)
    y_buff[0] = y2
    for i in range(4, 6):
        buff_idx = i - 4
        x_body1 = x_buff[buff_idx]
        y_body1 = y_buff[buff_idx]
        x_body2 = x_body1 + i
        x_body3 = x_body2 + y_body1
        y_body2 = i
        y_body3 = y_body2 + x_body3
        next_idx = buff_idx + 1
        x_buff[next_idx] = x_body3
        y_buff[next_idx] = y_body3
    x3 = x_buff[size]
    y3 = y_buff[size]
    assert x3 == 35
    assert y3 == 40
    return
```

Finally, transform the loop into a recursive function:

```
def main():
    x = 0
    y = 3
    x2 = x + y
    y2 = y + x2
    size = 6 - 4
    x_buff = Array(size + 1)
    x_buff[0] = x2
    y_buff = Array(size + 1)
    y_buff[0] = y2
    loop(4, x_buff, y_buff)
    x3 = x_buff[size]
    y3 = y_buff[size]
    assert x3 == 35
    assert y3 == 40
    return

def loop(i, x_buff, y_buff):
    if i == 6:
        return
    else:
        buff_idx = i - 4
        x_body1 = x_buff[buff_idx]
        y_body1 = y_buff[buff_idx]
        x_body2 = x_body1 + i
        x_body3 = x_body2 + y_body1
        y_body2 = i
        y_body3 = y_body2 + x_body3
        next_idx = buff_idx + 1
        x_buff[next_idx] = x_body3
        y_buff[next_idx] = y_body3
        loop(i + 1, x_buff, y_buff)
    return
```

