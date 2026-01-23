from snark_lib import *


# Error test: pop on empty vector
def main():
    v = DynArray([])
    v.pop()
    return
