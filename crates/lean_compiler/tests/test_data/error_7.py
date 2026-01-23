from snark_lib import *


# Error: inline functions with parameters: Mut are not supported
def main():
    return


@inline
def double(x: Mut):
    x = x * 2
    return x
