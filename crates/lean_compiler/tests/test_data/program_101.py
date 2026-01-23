from snark_lib import *
def main():
    x: Mut = 5

    cond = 1
    if cond == 1:
        x = x + 10
    else:
    assert x == 15

    y: Mut = 5
    cond2 = 0
    if cond2 == 1:
        y = y + 10
    else:
    assert y == 5

    return