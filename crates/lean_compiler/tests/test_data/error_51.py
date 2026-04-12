from snark_lib import *


# Error: regression test — after a loop with a write-only mut var, the final
# value should be the loop's last write, not the pre-loop value.
def main():
    x: Mut = 100
    for i in range(0, 5):
        x = i
    # Last write: x = 4. Claim x == 100 is wrong.
    assert x == 100
    return
