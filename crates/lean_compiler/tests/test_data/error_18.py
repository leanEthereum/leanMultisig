from snark_lib import *


# Error: push to outer-scope vector inside non-unrolled loop
def main():
    v = DynArray([1, 2, 3])  # Vector in outer scope
    for i in range(0, 5):
        v.push(i)  # Error: cannot push to outer-scope vector inside non-unrolled loop
    return
