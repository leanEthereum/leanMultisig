from snark_lib import *


# Test vector with expression using loop variable
def main():
    # Build Fibonacci-like sequence using vector
    fib = DynArray([1, 1])
    for i in unroll(2, 8):
        fib.push(fib[i - 1] + fib[i - 2])

    assert len(fib) == 8
    assert fib[0] == 1
    assert fib[1] == 1
    assert fib[2] == 2
    assert fib[3] == 3
    assert fib[4] == 5
    assert fib[5] == 8
    assert fib[6] == 13
    assert fib[7] == 21
    return
