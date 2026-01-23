from snark_lib import *
# Test: bad indentation - dedent closes function too early, leaving code at program level
def main():
    x = 1
        y = 2
    return
