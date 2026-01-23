from snark_lib import *
def main():
    assert func(0) == 11
    assert func(1) == 40
    assert func(2) == 10
    return

def func(i):
    x: Mut = 10
    match i:
        case 0:
            x = x + 1
        case 1:
            if 1 == 0:
                x = x + 100
            else:
                x = x + 10
            if 1 == 0:

            else:
                x = x + 10
            if 1 == 1:
                if 1 == 0:

                else:
                    x = x + 10
            else:

        case 2:
    return x