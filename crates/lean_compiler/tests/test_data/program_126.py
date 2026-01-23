from snark_lib import *


def main():
    result1 = match_on_loop_var()
    assert result1 == 100

    result2 = match_computed_selector()
    assert result2 == 10

    result3 = match_complex_selector()
    assert result3 == 222

    return


def match_on_loop_var():
    acc: Mut = 0
    for i in unroll(0, 2):
        match i:
            case 0:
                acc = acc + i  # acc = 0
            case 1:
                acc = acc + 100  # acc = 100
    return acc


def match_computed_selector():
    acc: Mut = 0
    for i in unroll(0, 4):
        selector = i % 2  # Use actual modulo
        match selector:
            case 0:
                acc = acc + i
            case 1:
                acc = acc + i * 2
    return acc


def match_complex_selector():
    sum: Mut = 0
    for i in unroll(0, 6):
        selector = i % 3
        match selector:
            case 0:
                sum = sum + 1  # i=0,3: sum += 2
            case 1:
                sum = sum + 10  # i=1,4: sum += 20
            case 2:
                sum = sum + 100  # i=2,5: sum += 200
    return sum
