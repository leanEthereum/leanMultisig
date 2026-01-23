from snark_lib import *


# Test building vector and then reading in separate unrolled loops
def main():
    # Build a vector of squares
    squares = DynArray([])
    for i in unroll(0, 6):
        squares.push(i * i)

    # Verify in a separate loop
    for i in unroll(0, 6):
        assert squares[i] == i * i

    # Also check len
    assert len(squares) == 6
    return
