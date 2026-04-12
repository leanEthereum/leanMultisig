from snark_lib import *

# Error: 'or' conditions must be fully resolvable at compile time.
# Here 'a' is a runtime variable, so the 'or' cannot be eliminated.
def main():
    a = 0
    a = zero()
    if a == 1 or 1 == 1:
        b = 10
    return

def zero():
    return 0