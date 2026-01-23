from snark_lib import *


# Error: push to outer-scope vector inside else branch
def main():
    v = DynArray([1, 2, 3])  # Vector in outer scope
    x = 5
    if x == 5:
        x = 6
    else:
        v.push(4)  # Error: cannot push to outer-scope vector inside if/else
    return
