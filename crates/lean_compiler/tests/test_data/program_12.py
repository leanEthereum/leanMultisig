from snark_lib import *
N = 10

def main():
    arr = Array(N)
    fill_array(arr)
    print_array(arr)
    return

def fill_array(arr):
    for i in range(0, N):
        if i == 0:
            arr[i] = 10
        else if i == 1:
            arr[i] = 20
        else if i == 2:
            arr[i] = 30
        else:
            i_plus_one = i + 1
            arr[i] = i_plus_one
    return

def print_array(arr):
    for i in range(0, N):
        arr_i = arr[i]
        print(arr_i)
    return