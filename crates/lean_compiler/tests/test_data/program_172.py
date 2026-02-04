from snark_lib import *

# Test match_range feature


def helper_const(n: Const):
    return n * 10


def main():
    # Test 1: Basic match_range - no forward declaration needed (auto-generated as Imu)
    x = 2
    r1 = match_range(x, range(0, 4), lambda i: i * 100)
    assert r1 == 200

    # Test 2: match_range with non-zero start range
    y = 5
    r2 = match_range(y, range(3, 7), lambda j: j + 1000)
    assert r2 == 1005

    # Test 3: match_range calling a function with const parameter
    z = 1
    r3 = match_range(z, range(0, 3), lambda k: helper_const(k))
    assert r3 == 10

    # Test 4: match_range with expression as value
    a = 3
    b = 1
    r4 = match_range(a - b, range(0, 4), lambda n: n * n)
    assert r4 == 4  # (3-1)=2, 2*2=4

    # Test 5: Nested expressions in lambda body
    c = 2
    r5 = match_range(c, range(0, 3), lambda m: m * m + m + 1)
    assert r5 == 7  # 2*2 + 2 + 1 = 7

    # Test 6: match_range with multiple continuous ranges
    d = 0
    r6a = match_range(d, range(0, 2), lambda i: 100 + i, range(2, 5), lambda i: 200 + i)
    assert r6a == 100  # d=0 -> 100+0=100

    e = 3
    r6b = match_range(e, range(0, 2), lambda i: 100 + i, range(2, 5), lambda i: 200 + i)
    assert r6b == 203  # e=3 -> 200+3=203

    # Test 7: match_range with different lambdas calling functions
    f = 1
    r7 = match_range(f, range(0, 1), lambda i: 999, range(1, 4), lambda i: helper_const(i))
    assert r7 == 10  # f=1 -> helper_const(1)=10

    # Test 8: match_range first range (special case)
    g = 0
    r8 = match_range(g, range(0, 1), lambda i: 42, range(1, 3), lambda i: i * 7)
    assert r8 == 42  # g=0 -> 42

    # Test 9: Results are always immutable
    m = 1
    r9 = match_range(m, range(0, 3), lambda i: i * 7)
    assert r9 == 7
    # r9 = 999  # Would be an error - match_range results are always immutable

    # ========== MULTIPLE RETURN VALUES TESTS ==========

    # Test 10: Basic multiple return values (2 values)
    v10 = 1
    a10, b10 = match_range(v10, range(0, 3), lambda i: two_values_const(i))
    assert a10 == 10  # 1 * 10
    assert b10 == 101  # 1 + 100

    # Test 11: Multiple return values with different case
    v11 = 2
    a11, b11 = match_range(v11, range(0, 3), lambda i: two_values_const(i))
    assert a11 == 20  # 2 * 10
    assert b11 == 102  # 2 + 100

    # Test 12: Three return values
    v12 = 1
    x12, y12, z12 = match_range(v12, range(0, 3), lambda i: three_values_const(i))
    assert x12 == 1  # i
    assert y12 == 10  # i * 10
    assert z12 == 1001  # i + 1000

    # Test 13: Multiple return values with multiple ranges
    v13 = 3
    a13, b13 = match_range(v13, range(0, 2), lambda i: pair_small(i), range(2, 5), lambda i: pair_large(i))
    assert a13 == 300  # 3 * 100 (pair_large)
    assert b13 == 3000  # 3 * 1000

    # Test 14: Multiple return values with multiple ranges - different range
    v14 = 1
    a14, b14 = match_range(v14, range(0, 2), lambda i: pair_small(i), range(2, 5), lambda i: pair_large(i))
    assert a14 == 1  # 1 * 1 (pair_small)
    assert b14 == 10  # 1 * 10

    # Test 15: Multiple return values - edge case first element
    v15 = 0
    a15, b15 = match_range(v15, range(0, 4), lambda i: two_values_const(i))
    assert a15 == 0
    assert b15 == 100

    # Test 16: Multiple return values - edge case last element
    v16 = 2
    a16, b16 = match_range(v16, range(0, 3), lambda i: two_values_const(i))
    assert a16 == 20
    assert b16 == 102

    # Test 17: Four return values
    v17 = 1
    p17, q17, r17, s17 = match_range(v17, range(0, 3), lambda i: four_values_const(i))
    assert p17 == 1
    assert q17 == 2
    assert r17 == 3
    assert s17 == 4

    # Test 18: Multiple return with expression in match value
    v18a = 5
    v18b = 3
    a18, b18 = match_range(v18a - v18b, range(0, 4), lambda i: two_values_const(i))
    assert a18 == 20  # (5-3)=2, 2*10=20
    assert b18 == 102

    # Test 19: Nested match_range results used in computation
    v19 = 1
    x19, y19 = match_range(v19, range(0, 3), lambda i: two_values_const(i))
    result19 = x19 + y19
    assert result19 == 111  # 10 + 101

    # Test 20: Three values with multiple ranges
    v20 = 4
    x20, y20, z20 = match_range(
        v20, range(0, 3), lambda i: three_values_const(i), range(3, 6), lambda i: three_values_offset(i)
    )
    assert x20 == 104  # 4 + 100
    assert y20 == 1004  # 4 + 1000
    assert z20 == 10004  # 4 + 10000

    # ========== INLINED FUNCTION TESTS ==========

    # Test 21: Basic inlined function - single return value
    v21 = 2
    r21 = match_range(v21, range(0, 4), lambda i: inlined_single(i))
    assert r21 == 200  # 2 * 100

    # Test 22: Inlined function - two return values
    v22 = 3
    a22, b22 = match_range(v22, range(0, 5), lambda i: inlined_pair(i))
    assert a22 == 30  # 3 * 10
    assert b22 == 300  # 3 * 100

    # Test 23: Inlined function with multiple ranges
    v23 = 4
    r23 = match_range(v23, range(0, 3), lambda i: inlined_small(i), range(3, 6), lambda i: inlined_large(i))
    assert r23 == 4000  # 4 * 1000 (inlined_large)

    # Test 24: Inlined function - first range
    v24 = 1
    r24 = match_range(v24, range(0, 3), lambda i: inlined_small(i), range(3, 6), lambda i: inlined_large(i))
    assert r24 == 10  # 1 * 10 (inlined_small)

    # Test 25: Inlined function with three return values
    v25 = 2
    x25, y25, z25 = match_range(v25, range(0, 4), lambda i: inlined_triple(i))
    assert x25 == 2  # i
    assert y25 == 20  # i * 10
    assert z25 == 200  # i * 100

    # Test 26: Inlined function with complex body
    v26 = 3
    r26 = match_range(v26, range(0, 5), lambda i: inlined_complex(i))
    assert r26 == 39  # 3*3 + 3*10 = 9 + 30 = 39

    # Test 27: Mix of inlined and const functions in multiple ranges
    v27 = 2
    a27, b27 = match_range(v27, range(0, 2), lambda i: inlined_pair(i), range(2, 5), lambda i: two_values_const(i))
    assert a27 == 20  # 2 * 10 (two_values_const)
    assert b27 == 102  # 2 + 100

    # Test 28: Inlined with expression as match value
    v28a = 7
    v28b = 4
    r28 = match_range(v28a - v28b, range(0, 5), lambda i: inlined_single(i))
    assert r28 == 300  # (7-4)=3, 3*100=300

    # Test 29: Inlined function result used in computation
    v29 = 1
    x29, y29 = match_range(v29, range(0, 3), lambda i: inlined_pair(i))
    result29 = x29 * y29
    assert result29 == 1000  # 10 * 100 = 1000

    # Test 30: Nested inlined - inlined calling another inlined
    v30 = 2
    r30 = match_range(v30, range(0, 4), lambda i: inlined_nested(i))
    assert r30 == 2000  # inlined_single(2) * 10 = 200 * 10 = 2000

    return


@inline
def inlined_single(n):
    return n * 100


@inline
def inlined_pair(n):
    return n * 10, n * 100


@inline
def inlined_small(n):
    return n * 10


@inline
def inlined_large(n):
    return n * 1000


@inline
def inlined_triple(n):
    return n, n * 10, n * 100


@inline
def inlined_complex(n):
    a = n * n
    b = n * 10
    return a + b


@inline
def inlined_nested(n):
    x = inlined_single(n)
    return x * 10


def two_values_const(n: Const):
    return n * 10, n + 100


def three_values_const(n: Const):
    return n, n * 10, n + 1000


def four_values_const(n: Const):
    return n, n * 2, n * 3, n * 4


def pair_small(n: Const):
    return n * 1, n * 10


def pair_large(n: Const):
    return n * 100, n * 1000


def three_values_offset(n: Const):
    return n + 100, n + 1000, n + 10000
