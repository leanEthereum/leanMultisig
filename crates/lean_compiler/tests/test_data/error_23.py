from snark_lib import *


# Error test: pop from outer-scope vector in non-unroll loop
def main():
    v = DynArray([1, 2, 3])
    for i in range(0, 2):
        v.pop()
    return
