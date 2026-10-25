#!/bin/bash

# Tests that Fjalar traces variables and formal parameters of type _Float128
# (IEEE 754 binary128), which has the size of a long double on amd64, so
# Fjalar distinguishes it by name.  Kvasir must print each value rounded to a
# double (including one too large for a double, and a subnormal double) and
# give each variable the rep-type double.  Fjalar cannot read a _Float128
# return value, which is in all 16 bytes of xmm0, so it must omit the return
# value.

exec "$(dirname "$0")/float-types-driver.sh" float128
