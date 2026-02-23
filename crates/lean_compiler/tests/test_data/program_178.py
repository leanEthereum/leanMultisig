from snark_lib import *

def main():
    n = 10
    i: Mut = 0
    if 1 == one():
        for j in unroll(0, n):
            i += j
    assert i == 45
    return

def one():
    return 1