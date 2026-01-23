from snark_lib import *


# Test: local vectors inside if/else branches are allowed
def main():
    x = 5
    if x == 5:
        # Local vector in then branch - allowed
        v = DynArray([1, 2, 3])
        v.push(4)
        assert v[3] == 4
        assert len(v) == 4
        w = DynArray([])
        w.push(100)
        assert w[0] == 100
    else:
        # Different local vector in else branch - allowed (no clash, different control flow)
        w = DynArray([10, 20])
        w.push(30)
        assert w[2] == 30
    return
