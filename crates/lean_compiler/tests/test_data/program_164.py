from snark_lib import *

# Test: nested compile-time conditions
A = 1
B = 2


def main():
    v = DynArray([])
    if A == 1:
        if B == 2:
            v.push(100)  # OK: both conditions are compile-time true
        else:
            v.push(200)
    else:
        v.push(300)
    assert v[0] == 100
    return
