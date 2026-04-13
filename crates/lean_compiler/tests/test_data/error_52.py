from snark_lib import *


# Error: write-only mut var update in an if-branch must propagate out.
def main():
    x: Mut = 0
    cond = one()
    if cond == 1:
        x = 42
    # x should be 42 after the branch. Claim x == 0 is wrong.
    assert x == 0
    return


def one():
    return 1
