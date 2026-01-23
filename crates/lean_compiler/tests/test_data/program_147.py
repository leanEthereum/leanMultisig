from snark_lib import *


# Test .push() on vectors
def main():
    v = DynArray([1, 2, 3])
    assert len(v) == 3
    v.push(4)
    assert len(v) == 4
    assert v[3] == 4
    v.push(5)
    assert len(v) == 5
    assert v[4] == 5
    return
