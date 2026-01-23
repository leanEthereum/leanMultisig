from snark_lib import *
# Test: Mutable variables in non-unrolled loops
# This tests the automatic buffer transformation for mutable variables


def main():
    x: Mut = 0
    y: Mut = 3
    x += y
    y += x
    assert x == 3
    assert y == 6
    for i in range(4, 6):
        x += i
        x += y
        y = i
        y += x
    assert x == 35
    assert y == 40
    return
