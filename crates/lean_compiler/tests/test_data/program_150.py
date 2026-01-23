from snark_lib import *


# Test vectors with unrolled loops
def main():
    v = DynArray([])
    for i in unroll(0, 5):
        v.push(i * 2)
    assert len(v) == 5
    assert v[0] == 0
    assert v[1] == 2
    assert v[2] == 4
    assert v[3] == 6
    assert v[4] == 8
    return
