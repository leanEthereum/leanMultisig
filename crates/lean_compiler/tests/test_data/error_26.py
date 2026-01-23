from snark_lib import *
# Test: bad indentation - dedent closes function and loop too early
def main():
    for i in unroll(0, 3):
        x = i
y = 0
    return
