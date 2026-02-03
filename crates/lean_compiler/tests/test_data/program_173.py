from snark_lib import *

# Test match_range with non-zero starting indices


def main():
    # Test 1: Range starting at 1
    x1 = 2
    r1 = match_range(x1, range(1, 5), lambda i: i * 10)
    assert r1 == 20  # 2 * 10

    # Test 2: Range starting at 1, first element
    x2 = 1
    r2 = match_range(x2, range(1, 5), lambda i: i * 100)
    assert r2 == 100  # 1 * 100

    # Test 3: Range starting at 1, last element
    x3 = 4
    r3 = match_range(x3, range(1, 5), lambda i: i + 1000)
    assert r3 == 1004  # 4 + 1000

    # Test 4: Range starting at 3
    x4 = 5
    r4 = match_range(x4, range(3, 8), lambda i: i * i)
    assert r4 == 25  # 5 * 5

    # Test 5: Range starting at 10
    x5 = 12
    r5 = match_range(x5, range(10, 15), lambda i: i - 10)
    assert r5 == 2  # 12 - 10

    # Test 6: Multiple ranges, first starting at non-zero
    x6 = 2
    r6 = match_range(x6, range(1, 3), lambda i: i * 10, range(3, 6), lambda i: i * 100)
    assert r6 == 20  # 2 * 10

    # Test 7: Multiple ranges, selecting from second range
    x7 = 4
    r7 = match_range(x7, range(1, 3), lambda i: i * 10, range(3, 6), lambda i: i * 100)
    assert r7 == 400  # 4 * 100

    # Test 8: Non-zero start with multiple return values
    x8 = 3
    a8, b8 = match_range(x8, range(1, 5), lambda i: two_vals(i))
    assert a8 == 30  # 3 * 10
    assert b8 == 300  # 3 * 100

    # Test 9: Non-zero start with three return values
    x9 = 2
    p9, q9, r9 = match_range(x9, range(1, 4), lambda i: three_vals(i))
    assert p9 == 2  # i
    assert q9 == 20  # i * 10
    assert r9 == 200  # i * 100

    # Test 10: Non-zero start with expression as match value
    a10 = 7
    b10 = 3
    r10 = match_range(a10 - b10, range(2, 6), lambda i: i * 11)
    assert r10 == 44  # (7-3)=4, 4*11=44

    # Test 11: Non-zero start with inlined function
    x11 = 3
    r11 = match_range(x11, range(1, 5), lambda i: inlined_mul(i))
    assert r11 == 300  # 3 * 100

    # Test 12: Large non-zero start (simulating real use case like domain_size)
    x12 = 15
    r12 = match_range(x12, range(10, 20), lambda i: 2 ** (i - 10))
    assert r12 == 32  # 2^5 = 32

    # Test 13: Multiple return values with multiple non-zero ranges
    x13 = 5
    a13, b13 = match_range(x13, range(2, 4), lambda i: pair_small(i), range(4, 7), lambda i: pair_large(i))
    assert a13 == 500  # 5 * 100
    assert b13 == 5000  # 5 * 1000

    # Test 14: First range selected in multiple non-zero ranges
    x14 = 3
    a14, b14 = match_range(x14, range(2, 4), lambda i: pair_small(i), range(4, 7), lambda i: pair_large(i))
    assert a14 == 3  # 3 * 1
    assert b14 == 30  # 3 * 10

    return


def two_vals(n: Const):
    return n * 10, n * 100


def three_vals(n: Const):
    return n, n * 10, n * 100


def pair_small(n: Const):
    return n * 1, n * 10


def pair_large(n: Const):
    return n * 100, n * 1000


@inline
def inlined_mul(n):
    return n * 100
