from snark_lib import *
# Test pushing to nested vectors in unrolled loops

ARR = [3, 4, 5]


def main():
    # Create a 3-element vector of empty vectors
    rows = DynArray([DynArray([]), DynArray([]), DynArray([])])

    # Fill each row with its index repeated
    for i in unroll(0, 3):
        for j in unroll(0, 3):
            rows[i].push(i + len(ARR) - 1 + ARR[0] - 3 + j - 2)

    # Verify structure
    assert len(rows) == 3
    assert len(rows[0]) == 3
    assert len(rows[1]) == 3
    assert len(rows[2]) == 3

    # Verify values: rows[i][j] == i + j
    assert rows[0][0] == 0
    assert rows[0][1] == 1
    assert rows[0][2] == 2
    assert rows[1][0] == 1
    assert rows[1][1] == 2
    assert rows[1][len(ARR) - 1 + ARR[0] - 3] == 3
    assert rows[2][0] == 2
    assert rows[2][1] == 3
    assert rows[2][2] == 4

    return
