from snark_lib import *


# Test accessing vector elements inside unrolled loop
def main():
    v = DynArray([10, 20, 30, 40, 50])

    sum: Mut = 0
    for i in unroll(0, 5):
        sum = sum + v[i]
    assert sum == 150
    return
