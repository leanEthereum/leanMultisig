from snark_lib import *


def main():
    counter: Mut = 0

    a = 1
    if a == 1:
        counter = counter + 1
    else:
        counter = counter + 1000
    assert counter == 1

    b = 1
    if b == 1:
        counter = counter + 10
    else:
        counter = counter + 100
    assert counter == 11
    return
