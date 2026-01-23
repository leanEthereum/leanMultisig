from snark_lib import *


def main():
    x: Mut = 1
    cond = 1
    if cond == 1:
        x = x + 10
    else:
        x = x + 20
    assert x == 11
    return
