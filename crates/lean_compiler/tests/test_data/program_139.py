from snark_lib import *
# Test: Mutable variable with array operations inside non-unrolled loop


def main():
    arr = Array(5)
    arr[0] = 10
    arr[1] = 20
    arr[2] = 30
    arr[3] = 40
    arr[4] = 50

    sum: Mut = 0
    prev: Mut = 0
    for i in range(0, 5):
        val = arr[i]
        sum += val
        # Track running difference
        diff = val - prev
        prev = val
    # sum = 10 + 20 + 30 + 40 + 50 = 150
    # prev = 50 (last value)
    assert sum == 150
    assert prev == 50
    return
