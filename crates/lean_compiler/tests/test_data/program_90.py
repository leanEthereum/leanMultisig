from snark_lib import *


def main():
    total: Mut = 0
    for i in unroll(0, 3):
        match i:
            case 0:
                total = total + 1
            case 1:
                total = total + 10
            case 2:
                total = total + 100
    assert total == 111
    return
