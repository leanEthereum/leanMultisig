from snark_lib import *
# Test: Three levels of nested non-unrolled loops with mutable variable


def main():
    count: Mut = 0
    for i in range(0, 2):
        for j in range(0, 3):
            for k in range(0, 4):
                count += 1
    # Total iterations: 2 * 3 * 4 = 24
    assert count == 24
    return
