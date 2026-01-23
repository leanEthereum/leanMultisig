from snark_lib import *
def main():
    x1, y1, z1 = initial_values()
    assert x1 == 10
    assert y1 == 20
    assert z1 == 30

    x2, y2, z2 = rotate_triple(x1, y1, z1)
    assert x2 == 20
    assert y2 == 30
    assert z2 == 10

    x3, y3, z3 = scale_triple(x2, y2, z2, 2)
    assert x3 == 40
    assert y3 == 60
    assert z3 == 20

    a, b = swap_pair(100, 200)
    assert a == 200
    assert b == 100

    arr = Array(20)
    for i in unroll(0, 10):
        arr[i] = i * 5

    sum = sum_array_func(arr, 5)
    assert sum == 50

    result4 = complex_nested_compute(2, 1, 3)
    assert result4 == 280

    fwd_x: Imu
    fwd_y: Imu

    mode = 2
    if mode == 0:
        fwd_x = 1
        fwd_y = 1
    else if mode == 1:
        fwd_x = 10
        fwd_y = 10
    else:
        fwd_x = 100
        fwd_y = 200

    fwd_x2: Mut = fwd_x
    fwd_y2: Mut = fwd_y
    fwd_x2 = fwd_x2 + fwd_y2
    fwd_y2 = fwd_x2 - 100

    assert fwd_x2 == 300
    assert fwd_y2 == 200

    result6 = chain_of_funcs(5)
    assert result6 == 115

    p1, q1 = first_pair(3, 4)
    p2, q2 = second_pair(p1, q1)
    p3, q3 = third_pair(p2, q2)

    assert p3 == 103
    assert q3 == 1596

    return

def initial_values():
    return 10, 20, 30

def rotate_triple(a, b, c):
    return b, c, a

def scale_triple(a, b, c, factor):
    return a * factor, b * factor, c * factor

def swap_pair(a, b):
    return b, a

def sum_array_func(arr, n: Const):
    total: Mut = 0
    for i in unroll(0, n):
        total = total + arr[i]
    return total

def complex_nested_compute(outer, inner, depth):
    result: Imu

    if outer == 0:
        result = 100
    else if outer == 1:
        if inner == 0:
            result = 110
        else:
            result = 120
    else:
        if inner == 0:
            if depth == 0:
                result = 200
            else if depth == 1:
                result = 210
            else if depth == 2:
                result = 220
            else:
                result = 230
        else:
            if depth == 0:
                result = 250
            else if depth == 1:
                result = 260
            else if depth == 2:
                result = 270
            else:
                result = 280

    return result

def chain_of_funcs(x):
    y = step_one(x)
    z = step_two(y)
    w = step_three(z)
    return w

def step_one(n):
    return n + 10

def step_two(n):
    return n * 2

def step_three(n):
    return n + 85

def first_pair(a, b):
    return a + b, a * b

def second_pair(a, b):
    return a + b, a * b

def third_pair(a, b):
    return a + b, a * b