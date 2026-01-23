from snark_lib import *
# Test: Match with conditions inside non-unrolled loop


def main():
    a: Mut = 0
    b: Mut = 0
    for i in range(0, 3):
        match i:
            case 0:
                a += 1
                if a == 1:
                    b += 10
            case 1:
                a += 2
                if a == 3:
                    b += 20
            case 2:
                a += 4
                if a == 7:
                    b += 40
    # i=0: a=1, b=10
    # i=1: a=3, b=30
    # i=2: a=7, b=70
    assert a == 7
    assert b == 70
    return
