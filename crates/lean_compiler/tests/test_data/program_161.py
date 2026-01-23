from snark_lib import *

# Test: compile-time true condition allows push to outer-scope vector in then branch
FLAG = 1


def main():
    v = DynArray([1, 2, 3])
    if FLAG == 1:
        v.push(4)  # OK: condition is compile-time true, branch is inlined
    else:
        v.push(5)
    assert v[3] == 4
    return
