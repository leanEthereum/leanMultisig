from snark_lib import *


def main():
    x: Mut = 1
    cond = 1
    if cond == 1:
        x = x + 1
        x = x + 1
        x = x + 1
    else:
        x = x + 10
    assert x == 4

    y: Mut = 1
    cond2 = 0
    if cond2 == 1:
        y = y + 1
    else:
        y = y + 1
        y = y + 1
        y = y + 1
        y = y + 1
    assert y == 5
    return
