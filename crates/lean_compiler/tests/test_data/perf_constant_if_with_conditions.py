from snark_lib import *
# Complex test program with constant if/else conditions
# All conditions evaluate to constants at compile time and should be eliminated

A = 10
B = 20
C = 30
D = 5
ZERO = 0
ONE = 1

def main():
    result: Mut = 0

    # Simple constant condition (true)
    if A == 10:
        result = result + 1

    # Simple constant condition (false, no else)
    if A == 999:
        result = result + 1000

    # Constant condition with else (false branch taken)
    if D == 100:
        result = result + 2000
    else:
        result = result + 2

    # Nested constant conditions (all true)
    if A == 10:
        if B == 20:
            if C == 30:
                result = result + 4

    # Nested with mixed true/false (outer true, inner false)
    if A == 10:
        if B == 999:
            result = result + 3000
        else:
            result = result + 8

    # Using != operator (true)
    if A != 5:
        result = result + 16

    # Using != operator (false)
    if A != 10:
        result = result + 4000

    # Deeply nested (5 levels)
    if A == 10:
        if B == 20:
            if C == 30:
                if D == 5:
                    if ONE == 1:
                        result = result + 32

    # Chain of if-else-if with constants
    if A == 1:
        result = result + 5000
    elif A == 2:
        result = result + 6000
    elif A == 10:
        result = result + 64
    else:
        result = result + 7000

    # Nested false conditions (entire block should be eliminated)
    if ZERO == 1:
        if A == 10:
            if B == 20:
                result = result + 8000

    # Complex: true outer, false inner with else
    if B == 20:
        if C == 999:
            result = result + 9000
        else:
            if D == 5:
                result = result + 128

    # Final result should be: 1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 = 255
    assert result == 255
    return