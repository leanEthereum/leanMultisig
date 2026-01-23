from snark_lib import *


# Test basic DynArray([]) creation and indexing
def main():
    v = DynArray([1, 2, 3])
    assert v[0] == 1
    assert v[1] == 2
    assert v[2] == 3
    assert len(v) == 3
    return
