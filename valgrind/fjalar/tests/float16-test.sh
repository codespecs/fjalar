#!/bin/bash

# Tests that Fjalar traces variables, formal parameters, and return values of
# the 2-byte floating-point types _Float16 (IEEE 754 binary16) and __bf16
# (bfloat16).  The two types have the same size and DWARF encoding, so Fjalar
# distinguishes them by name.  Kvasir must print each value as a double
# (including infinity, NaN, and a subnormal value) and give each variable the
# rep-type double.

exec "$(dirname "$0")/float-types-driver.sh" float16
