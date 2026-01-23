from snark_lib import *
def main():
    assert func(0) == 11
    assert func(1) == 20
    assert func(2) == 10
    return

def func(i):
    x: Mut = 10
    match i:
        case 0:
            x = x + 1
        case 1:
            x = x + 10
        case 2:
    return x