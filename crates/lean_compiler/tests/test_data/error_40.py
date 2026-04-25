from snark_lib import *


# Error: assertion on a mutable accumulator after a loop must fail at runtime.
def main():
    acc: Mut = 0
    for i in range(0, 5):
        acc += i
    # Actual sum is 0+1+2+3+4 = 10
    assert acc == 999
    return
