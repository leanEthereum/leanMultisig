from snark_lib import *

# Test: compile-time condition using const array access
ARR = [0, 1, 2]


def main():
    v = DynArray([])
    v.push(10)
    if ARR[1] == 1:
        v.push(20)  # OK: ARR[1] == 1 is compile-time true
    else:
        v.push(30)
    assert v[0] == 10
    assert v[1] == 20
    return
