from snark_lib import *


def main():
    x: Mut = 5
    x = x + 1
    assert x == 6
    return
