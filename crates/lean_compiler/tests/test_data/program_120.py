from snark_lib import *


def main():
    final_state = state_machine(0)
    assert final_state == 3

    counter = counting_machine()
    assert counter == 10

    fib = fib_machine()
    assert fib == 13

    result = conditional_loop_machine()
    assert result == 45

    return


def state_machine(initial):
    state: Mut = initial
    for i in unroll(0, 3):
        state = state + 1
    return state


def counting_machine():
    counter: Mut = 0
    for i in unroll(0, 5):
        counter = counter + 1
        counter = counter + 1
    return counter


def fib_machine():
    a: Mut = 1
    b: Mut = 1
    for i in unroll(0, 5):
        temp = a + b
        a = b
        b = temp
    return b


def conditional_loop_machine():
    sum: Mut = 0
    for i in unroll(0, 10):
        sum = sum + i
    return sum
