from snark_lib import *


def main():
    x: Mut = 0

    a = 1
    if a == 1:
        x = x + 1
    else:
        x = x + 100

    b = 0
    if b == 1:
        x = x * 100
    else:
        x = x * 2

    c = 1
    if c == 1:
        x = x + 10
    else:
        x = x + 1000

    assert x == 12
    return
