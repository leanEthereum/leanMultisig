from snark_lib import *


# Test push with nested vectors
def main():
    v = DynArray([DynArray([1, 2])])
    assert len(v) == 1
    v.push(DynArray([3, 4]))
    assert len(v) == 2
    assert v[1][0] == 3
    assert v[1][1] == 4
    v.push(DynArray([5, 6, 7]))
    assert len(v) == 3
    assert len(v[2]) == 3
    assert v[2][2] == 7
    return
