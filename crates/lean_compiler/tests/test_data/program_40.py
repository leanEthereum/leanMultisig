from snark_lib import *


def main():
    x: Mut = 1
    x = x + 1
    x = x + 1
    assert x == 3
    return
