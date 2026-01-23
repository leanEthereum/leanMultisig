from snark_lib import *
# Test: Conditionals inside non-unrolled loop with mutable variables
# Tests if/else branches that modify mutable variables differently


def main():
    a: Mut = 0
    b: Mut = 100
    for i in range(0, 5):
        if i == 2:
            a += 10
            b -= 50
        else:
            a += 1
            b -= 1
    # i=0: a=1, b=99
    # i=1: a=2, b=98
    # i=2: a=12, b=48
    # i=3: a=13, b=47
    # i=4: a=14, b=46
    assert a == 14
    assert b == 46
    return
