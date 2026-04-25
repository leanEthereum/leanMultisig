from snark_lib import *

def main():
    arr = 1000
    arr[0] = 34
    v = read(arr)
    assert v == 34
    return


@inline
def read(a):
    return a[0]
