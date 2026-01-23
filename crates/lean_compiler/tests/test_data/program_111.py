from snark_lib import *
def main():
    fib_result = fib_iterative(10)
    assert fib_result == 55

    accum: Mut = 0
    for i in unroll(0, 5):
        accum = step_accumulate(accum, i)
    assert accum == 25

    a, b, c = chain_compute(5, 3)
    assert a == 11
    assert b == 3
    assert c == 39

    result = nested_mut_params(100)
    assert result == 106

    state: Mut = 0
    for phase in unroll(0, 5):
        state = state_machine_step(state, phase)
    assert state == 151

    x: Mut = 10
    y: Mut = 20

    cond1 = 1
    if cond1 == 1:
        x = x + y
        y = y - 5
    else:
        x = x * 2

    cond2 = 0
    if cond2 == 1:
        x = x * 100
    else:
        y = y + x

    assert x == 30
    assert y == 45

    sum_outer: Mut = 0
    sum_inner: Mut = 0
    for i in unroll(0, 3):
        sum_outer = sum_outer + i
        for j in unroll(0, 4):
            sum_inner = sum_inner + j
    assert sum_outer == 3
    assert sum_inner == 18

    result8 = complex_chain(2, 3, 5)
    assert result8 == 31

    return

def fib_iterative(n: Const):
    prev: Mut = 0
    curr: Mut = 1
    for i in unroll(0, n):
        if i == 0:
        else:
            next = prev + curr
            prev = curr
            curr = next
    return curr

def step_accumulate(acc, i):
    return acc + i * 2 + 1

def step_compute(x, y):
    sum = x + y
    product = x * y
    return sum, y, product

def chain_compute(x, y):
    a1, b1, c1 = step_compute(x, y)
    a2, b2, c2 = step_compute(a1, b1)
    return a2, b2, c1 + c2

def nested_mut_params(base: Mut):
    for i in unroll(0, 3):
        base = base + i * 2
    return base

def state_machine_step(current_state, phase):
    result: Imu
    if phase == 0:
        if current_state == 0:
            result = 1
        else:
            result = current_state + 1000
    else if phase == 1:
        result = current_state + 11
    else if phase == 2:
        result = current_state + 3
    else if phase == 3:
        result = current_state * 10
    else:
        result = current_state + 1
    return result

def complex_chain(a, b, c):
    sum = a + b
    product1 = sum * c
    product2 = a * b
    return product1 + product2