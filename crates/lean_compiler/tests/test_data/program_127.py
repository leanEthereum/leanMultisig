from snark_lib import *
def main():
    assert diamond_nested(0, 0) == 10
    assert diamond_nested(0, 1) == 20
    assert diamond_nested(1, 0) == 30
    assert diamond_nested(1, 1) == 40

    assert sequential_diamonds(0, 0) == 103
    assert sequential_diamonds(0, 1) == 105
    assert sequential_diamonds(1, 0) == 203
    assert sequential_diamonds(1, 1) == 205

    a, b, c = multi_var_diamond(0, 0)
    assert a == 1
    assert b == 10
    assert c == 100

    a2, b2, c2 = multi_var_diamond(1, 1)
    assert a2 == 4
    assert b2 == 40
    assert c2 == 400

    return

def diamond_nested(outer_cond, inner_cond):
    result: Mut = 0
    if outer_cond == 0:
        if inner_cond == 0:
            result = 10
        else:
            result = 20
    else:
        if inner_cond == 0:
            result = 30
        else:
            result = 40
    return result

def sequential_diamonds(cond1, cond2):
    x: Mut = 100

    if cond1 == 0:
        x = x + 1
    else:
        x = x + 101

    if cond2 == 0:
        x = x + 2
    else:
        x = x + 4

    return x

def multi_var_diamond(c1, c2):
    a: Mut = 0
    b: Mut = 0
    c: Mut = 0

    if c1 == 0:
        a = 1
        b = 10
        c = 100
    else:
        a = 2
        b = 20
        c = 200

    if c2 == 0:
    else:
        a = a * 2
        b = b * 2
        c = c * 2

    return a, b, c