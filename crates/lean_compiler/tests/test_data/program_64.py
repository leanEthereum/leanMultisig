from snark_lib import *
def main():
    for i in range(0, 6):
        x: Mut = i
        x = x + 1
        for j in range(0, 3):
            y: Mut = x + 1
            y = y + j
            if i == 10:
                y = y - 1
            if j == 10000:
                y = y - 2
            else if i != 1000:
                y = y + 2
            if j == 10000:
                y = y - 2
            else if i == 1000:
                y = y + 2
            if j == 10000:
                y = y - 2
            else if i != 1000:
                y = y + 2
            else:
                y = y + 2
            assert y == i + j + 6
    return