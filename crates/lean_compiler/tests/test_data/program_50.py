from snark_lib import *


def main():
    x: Mut = 0
    y: Mut = 0
    z: Mut = 0

    cond1 = 1
    if cond1 == 1:
        x = x + 10
        y = y + 20
    else:
        x = x + 100
        z = z + 30
    assert x == 10
    assert y == 20
    assert z == 0

    cond2 = 0
    if cond2 == 1:
        x = x + 1
    else:
        x = x + 2
        y = y + 3
    assert x == 12
    assert y == 23
    return
