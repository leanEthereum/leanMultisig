from snark_lib import *

# Test: inlined function containing match_range with lambda calling const function
# This tests the bug where lambda parameters were not renamed during inlining,
# causing const argument evaluation to fail.


def helper_const(n: Const):
    return n * n


def helper_const_two(a, n: Const):
    return a + n * 10


@inline
def inlined_with_match_range(x):
    res = match_range(x, range(1, 5), lambda i: helper_const(i))
    return res


@inline
def inlined_with_match_range_two_args(a, x):
    res = match_range(x, range(1, 5), lambda i: helper_const_two(a, i))
    return res


@inline
def inlined_with_match_range_multi_range(x):
    res = match_range(x, range(0, 3), lambda i: i * 10, range(3, 6), lambda i: helper_const(i))
    return res


@inline
def inlined_nested_match_range(x, y):
    r1 = match_range(x, range(1, 4), lambda i: helper_const(i))
    r2 = match_range(y, range(1, 4), lambda j: helper_const(j))
    return r1 + r2


def main():
    # Test 1: Basic inlined function with match_range calling const function
    r1 = inlined_with_match_range(2)
    assert r1 == 4  # 2*2

    r1b = inlined_with_match_range(3)
    assert r1b == 9  # 3*3

    # Test 2: Inlined function with match_range, lambda uses outer variable
    r2 = inlined_with_match_range_two_args(100, 2)
    assert r2 == 120  # 100 + 2*10

    r2b = inlined_with_match_range_two_args(50, 4)
    assert r2b == 90  # 50 + 4*10

    # Test 3: Inlined function with multiple ranges
    r3a = inlined_with_match_range_multi_range(1)
    assert r3a == 10  # 1*10 (first range)

    r3b = inlined_with_match_range_multi_range(4)
    assert r3b == 16  # 4*4 (second range, helper_const)

    # Test 4: Multiple calls to inlined function (tests unique renaming)
    a = inlined_with_match_range(1)
    b = inlined_with_match_range(2)
    c = inlined_with_match_range(3)
    assert a == 1  # 1*1
    assert b == 4  # 2*2
    assert c == 9  # 3*3

    # Test 5: Inlined function with two match_ranges
    r5 = inlined_nested_match_range(2, 3)
    assert r5 == 13  # 2*2 + 3*3 = 4 + 9

    # Test 6: Edge cases - first and last values
    first = inlined_with_match_range(1)
    last = inlined_with_match_range(4)
    assert first == 1  # 1*1
    assert last == 16  # 4*4

    return
