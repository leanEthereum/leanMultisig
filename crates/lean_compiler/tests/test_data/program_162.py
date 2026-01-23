from snark_lib import *

# Test: compile-time false condition allows push to outer-scope vector in else branch
FLAG = 0


def main():
    v = DynArray([1, 2, 3])
    if FLAG == 1:
        v.push(4)
    else:
        v.push(5)  # OK: condition is compile-time false, else branch is inlined
    assert v[3] == 5
    return
