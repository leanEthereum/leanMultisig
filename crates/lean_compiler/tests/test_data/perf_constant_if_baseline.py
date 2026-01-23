from snark_lib import *
# Baseline program - equivalent to perf_constant_if_with_conditions.py
# after all constant if/else conditions are eliminated at compile time
#
# This is what the optimized version should compile down to


def main():
    result: Mut = 0

    # From: if A == 10 { result = result + 1; }
    result = result + 1

    # From: if D == 100 { ... } else { result = result + 2; }
    result = result + 2

    # From: nested if A == 10, B == 20, C == 30
    result = result + 4

    # From: if A == 10 { if B == 999 { ... } else { result = result + 8; } }
    result = result + 8

    # From: if A != 5 { result = result + 16; }
    result = result + 16

    # From: deeply nested (5 levels all true)
    result = result + 32

    # From: if-else-if chain where A == 10
    result = result + 64

    # From: if B == 20 { if C == 999 { ... } else { if D == 5 { result = result + 128; } } }
    result = result + 128

    # Final result should be: 1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 = 255
    assert result == 255
    return
