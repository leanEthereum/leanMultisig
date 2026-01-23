from snark_lib import *


# Test nested vectors
def main():
    v = DynArray([DynArray([1, 2]), DynArray([3, 4, 5])])
    assert len(v) == 2
    assert len(v[0]) == 2
    assert len(v[1]) == 3
    assert v[0][0] == 1
    assert v[0][1] == 2
    assert v[1][0] == 3
    assert v[1][2] == 5
    return
