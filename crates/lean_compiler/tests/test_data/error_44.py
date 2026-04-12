from snark_lib import *


# Error: assertion inside an unroll must fail at runtime on the matching iteration.
def main():
    arr = Array(4)
    arr[0] = 10
    arr[1] = 20
    arr[2] = 30
    arr[3] = 40
    for i in unroll(0, 4):
        v = arr[i]
        # Claim: all entries equal 99 — false for every iteration.
        assert v == 99
    return
