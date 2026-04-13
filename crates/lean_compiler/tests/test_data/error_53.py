from snark_lib import *


# Error: nested loops with write-only mut var must still propagate the final value.
def main():
    v: Mut = 0
    for i in range(0, 3):
        for j in range(0, 2):
            v = i * 10 + j
    # Last iteration: i=2, j=1 -> v = 21. Claim v == 0 is wrong.
    assert v == 0
    return
