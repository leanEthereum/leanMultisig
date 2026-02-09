from snark_lib import *

# Comprehensive test for dynamic_unroll
# Tests: edge cases, mutable accumulators, array writes, nested dynamic_unroll,
#        multiple dynamic_unrolls in one function, conditional body logic,
#        interaction with regular unroll, and varying n_bits.
#
# Note: n_bits should be kept small (<=8) since the generated code size is O(2^n_bits).


def main():
    # --- Edge cases ---
    # a = 0: no iterations
    z = sum_up_to(0, 4)
    assert z == 0

    # a = 1: single iteration (only i=0)
    z1 = sum_up_to(1, 4)
    assert z1 == 0

    # a = 2: two iterations
    z2 = sum_up_to(2, 4)
    assert z2 == 1

    # a = 2^n_bits - 1: max value for n_bits=4
    z15 = sum_up_to(15, 4)
    assert z15 == 105

    # power of two
    z8 = sum_up_to(8, 4)
    assert z8 == 28

    # --- Basic accumulation with n_bits=8 ---
    z7 = sum_up_to(7, 8)
    assert z7 == 21

    z100 = sum_up_to(100, 8)
    assert z100 == 4950

    # --- Array writes via dynamic_unroll ---
    buf = Array(16)
    fill_squares(buf, 10, 4)
    assert buf[0] == 0
    assert buf[1] == 1
    assert buf[4] == 16
    assert buf[9] == 81

    # --- Nested dynamic_unroll (triangular sum) ---
    # for i in 0..a: for j in 0..i: total += 1
    # i=0: 0, i=1: 1, i=2: 2, i=3: 3, i=4: 4 => 10
    tri = triangular(5, 4)
    assert tri == 10
    tri0 = triangular(0, 4)
    assert tri0 == 0
    tri1 = triangular(1, 4)
    assert tri1 == 0
    tri2 = triangular(2, 4)
    assert tri2 == 1

    # --- Two sequential dynamic_unrolls in one function ---
    r = double_loop(3, 5, 4)
    # first loop: 0+1+2 = 3, second loop: 5*1 = 5, total = 8
    assert r == 8
    # edge: both zero
    r0 = double_loop(0, 0, 4)
    assert r0 == 0

    # --- Conditional body: only accumulate even indices ---
    e = sum_even_indices(8, 4)
    # even indices in 0..8: 0,2,4,6 => sum = 12
    assert e == 12
    e0 = sum_even_indices(0, 4)
    assert e0 == 0
    e1 = sum_even_indices(1, 4)
    assert e1 == 0

    # --- dynamic_unroll writing to array + reading back ---
    check = Array(8)
    write_and_verify(check, 6, 4)

    # --- dynamic_unroll with arithmetic in body ---
    poly = eval_polynomial(5, 4)
    # sum of i^2 for i in 0..5: 0+1+4+9+16 = 30
    assert poly == 30

    # --- Nested: outer dynamic_unroll, inner regular unroll ---
    m = mixed_loops(4, 4)
    # for i in 0..4: for j in unroll(0,3): acc += i+j
    # i=0: 0+1+2=3, i=1: 1+2+3=6, i=2: 2+3+4=9, i=3: 3+4+5=12 => 30
    assert m == 30

    # --- Called with different n_bits for same function ---
    s4 = sum_up_to(10, 4)
    assert s4 == 45
    s8 = sum_up_to(10, 8)
    assert s8 == 45

    # --- Complex body: sum of squares with algebraic verification ---
    sq = sum_squares(100, 8)
    # sum_{i=0}^{99} i^2 = 100*99*199/6 = 328350
    # Verify: 6 * sum == a*(a-1)*(2a-1)
    assert 6 * sq == 100 * 99 * 199

    # --- Complex body: array write + accumulate + read back ---
    work = Array(256)
    wa = write_and_accumulate(work, 50, 8)
    # Each entry: work[i] = i*i + 3*i + 7, sum of those for i in 0..50
    # sum = sum(i^2) + 3*sum(i) + 50*7 = 40425 + 3*1225 + 350 = 44450
    assert wa == 44450
    assert work[0] == 7
    assert work[1] == 11
    assert work[49] == 2555

    # --- Copy array region using dynamic_unroll ---
    src = Array(16)
    dst = Array(16)
    for i in unroll(0, 10):
        src[i] = (i + 1) * 7
    copy_array(src, dst, 10, 4)
    for i in unroll(0, 10):
        assert src[i] == dst[i]

    return


def sum_up_to(a, n_bits: Const):
    acc: Mut = 0
    for i in dynamic_unroll(0, a, n_bits):
        acc = acc + i
    return acc


def fill_squares(arr, n, n_bits: Const):
    for i in dynamic_unroll(0, n, n_bits):
        arr[i] = i * i
    return


def triangular(a, n_bits: Const):
    acc: Mut = 0
    for i in dynamic_unroll(0, a, n_bits):
        for j in dynamic_unroll(0, i, n_bits):
            acc = acc + 1
    return acc


def double_loop(a, b, n_bits: Const):
    acc: Mut = 0
    for i in dynamic_unroll(0, a, n_bits):
        acc = acc + i
    for j in dynamic_unroll(0, b, n_bits):
        acc = acc + 1
    return acc


def sum_even_indices(a, n_bits: Const):
    # Use bit decomposition to check parity: bits[0]==0 means even
    acc: Mut = 0
    for i in dynamic_unroll(0, a, n_bits):
        i_bits = Array(n_bits)
        LITTLE_ENDIAN = 1
        hint_decompose_bits(i, i_bits, n_bits, LITTLE_ENDIAN)
        i_ps = Array(n_bits)
        i_ps[0] = i_bits[0]
        assert i_ps[0] * (1 - i_ps[0]) == 0
        for k in unroll(1, n_bits):
            ib = i_bits[k]
            assert ib * (1 - ib) == 0
            i_ps[k] = i_ps[k - 1] + ib * 2**k
        assert i == i_ps[n_bits - 1]
        if i_bits[0] == 0:
            acc = acc + i
    return acc


def write_and_verify(arr, n, n_bits: Const):
    for i in dynamic_unroll(0, n, n_bits):
        arr[i] = i * 3 + 1
    assert arr[0] == 1
    assert arr[1] == 4
    assert arr[2] == 7
    assert arr[3] == 10
    assert arr[4] == 13
    assert arr[5] == 16
    return


def eval_polynomial(a, n_bits: Const):
    acc: Mut = 0
    for i in dynamic_unroll(0, a, n_bits):
        acc = acc + i * i
    return acc


def mixed_loops(a, n_bits: Const):
    # Outer: dynamic_unroll over runtime bound
    # Inner: regular unroll over compile-time bound
    acc: Mut = 0
    for i in dynamic_unroll(0, a, n_bits):
        for j in unroll(0, 3):
            acc = acc + i + j
    return acc


def sum_squares(a, n_bits: Const):
    acc: Mut = 0
    for i in dynamic_unroll(0, a, n_bits):
        acc = acc + i * i
    return acc


def write_and_accumulate(arr, n, n_bits: Const):
    acc: Mut = 0
    for i in dynamic_unroll(0, n, n_bits):
        val = i * i + 3 * i + 7
        arr[i] = val
        acc = acc + val
    return acc


def copy_array(src, dst, n, n_bits: Const):
    for i in dynamic_unroll(0, n, n_bits):
        dst[i] = src[i]
    return
