from snark_lib import *
# Test: Simple mutable variable in non-unrolled loop
# Sum of 1 to 10


def main():
    s: Mut = 0
    for i in range(1, 11):
        s += i
    assert s == 55
    return
