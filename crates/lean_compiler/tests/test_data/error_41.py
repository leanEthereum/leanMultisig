from snark_lib import *


# Error: assertion on the "last value" of a mutable var in a loop must fail at runtime.
def main():
    last: Mut = 0
    for i in range(0, 8):
        last = i * 2
    # Last iteration: i=7, last = 14
    assert last == 0
    return
