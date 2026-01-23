from snark_lib import *


# Error test: pop on empty nested vector
def main():
    v = DynArray([DynArray([])])
    v[0].pop()
    return
