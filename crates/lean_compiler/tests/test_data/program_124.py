from snark_lib import *


def main():
    r1 = five_deep_if(1, 1, 1, 1, 1)
    assert r1 == 11111

    r2 = five_deep_if(1, 1, 0, 0, 0)  # a=1,b=1: 10000+1000 = 11000
    assert r2 == 11000

    r3 = mixed_deep(0, 0, 0)
    assert r3 == 111

    r4 = mixed_deep(1, 1, 1)
    assert r4 == 222

    a, b = dual_mut_deep(0, 0)
    assert a == 110
    assert b == 1

    a2, b2 = dual_mut_deep(1, 1)
    assert a2 == 1
    assert b2 == 220

    return


def five_deep_if(a, b, c, d, e):
    x: Mut = 0
    if a == 1:
        x = x + 10000
        if b == 1:
            x = x + 1000
            if c == 1:
                x = x + 100
                if d == 1:
                    x = x + 10
                    if e == 1:
                        x = x + 1
    return x


def mixed_deep(outer_match, inner_if, innermost_match):
    x: Mut = 0
    match outer_match:
        case 0:
            x = x + 100
            if inner_if == 0:
                match innermost_match:
                    case 0:
                        x = x + 11
                    case 1:
                        x = x + 12
            else:
                match innermost_match:
                    case 0:
                        x = x + 21
                    case 1:
                        x = x + 22
        case 1:
            x = x + 200
            if inner_if == 0:
                match innermost_match:
                    case 0:
                        x = x + 11
                    case 1:
                        x = x + 12
            else:
                match innermost_match:
                    case 0:
                        x = x + 21
                    case 1:
                        x = x + 22
    return x


def dual_mut_deep(c1, c2):
    a: Mut = 1
    b: Mut = 1
    if c1 == 0:
        a = a + 100
        if c2 == 0:
            a = a + 9
        else:
            a = a + 19
    else:
        b = b + 200
        if c2 == 0:
            b = b + 9
        else:
            b = b + 19
    return a, b
