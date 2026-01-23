from snark_lib import *
def main():
    result1 = asymmetric_depth(0, 0, 0)
    assert result1 == 1111

    result2 = asymmetric_depth(0, 1, 1)
    assert result2 == 1122

    result3 = asymmetric_depth(1, 0, 0)  # Shallow branch
    assert result3 == 2000

    result4 = unbalanced_modifications(0)
    assert result4 == 25

    result5 = unbalanced_modifications(1)
    assert result5 == 110

    result6 = empty_else(0)
    assert result6 == 5

    result7 = empty_else(1)
    assert result7 == 15

    result8 = long_else_if_chain(0)
    assert result8 == 1

    result9 = long_else_if_chain(3)
    assert result9 == 4

    result10 = long_else_if_chain(5)
    assert result10 == 0

    return

def asymmetric_depth(outer, mid, inner):
    x: Mut = 1000
    if outer == 0:
        x = x + 100
        if mid == 0:
            x = x + 10
            if inner == 0:
                x = x + 1
            else:
                x = x + 2
        else:
            x = x + 20
            if inner == 0:
                x = x + 1
            else:
                x = x + 2
    else:
        x = 2000
    return x

def unbalanced_modifications(cond):
    x: Mut = 5
    if cond == 0:
        x = x + 5  # 10
        x = x * 2  # 20
        x = x + 5  # 25
    else:
        x = 110
    return x

def empty_else(cond):
    x: Mut = 5
    if cond == 1:
        x = x + 10
    return x

def long_else_if_chain(n):
    result: Mut = 0
    if n == 0:
        result = 1
    else if n == 1:
        result = 2
    else if n == 2:
        result = 3
    else if n == 3:
        result = 4
    else if n == 4:
        result = 5
    return result