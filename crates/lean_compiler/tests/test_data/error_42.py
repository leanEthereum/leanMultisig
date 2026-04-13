from snark_lib import *


# Error: assertion on an array element must fail at runtime.
def main():
    arr = Array(4)
    arr[0] = 11
    arr[1] = 22
    arr[2] = 33
    arr[3] = 44
    v = arr[2]
    assert v == 100
    return
