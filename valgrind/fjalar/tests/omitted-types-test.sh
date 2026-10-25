#!/bin/bash

# Tests that Fjalar omits variables, struct members, formal parameters, and
# return values of decimal floating-point types, GCC's complex integer
# types, and _BitInt(N) for N > 128, but reports a pointer to one, the other
# members of a struct, and the other formal parameters of a function.

exec "$(dirname "$0")/float-types-driver.sh" omitted-types
