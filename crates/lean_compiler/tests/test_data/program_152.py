from snark_lib import *


# Test vectors with nested unrolled loops
def main():
    v = DynArray([])
    for i in unroll(0, 3):
        for j in unroll(0, 2):
            v.push(i * 10 + j)
    assert len(v) == 6
    assert v[0] == 0  # i=0, j=0
    assert v[1] == 1  # i=0, j=1
    assert v[2] == 10  # i=1, j=0
    assert v[3] == 11  # i=1, j=1
    assert v[4] == 20  # i=2, j=0
    assert v[5] == 21  # i=2, j=1
    return
