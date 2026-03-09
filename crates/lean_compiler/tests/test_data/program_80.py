from snark_lib import *
def main():
    total: Mut = 0
    for i in unroll(0, 5):
        if i == 2:
            total = total + 100
        elif i == 4:
            total = total + 1000
        else:
            total = total + 1
    assert total == 1103
    return