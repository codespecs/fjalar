#!/bin/bash

# Tests that Fjalar traces variables and formal parameters of type long
# double.  Kvasir must print each value as a double and give each variable
# the rep-type double.  A long double's padding bytes need not be
# initialized.  Fjalar cannot read a long double return value, which is in
# the x87 register st(0), so it must omit the return value.

exec "$(dirname "$0")/float-types-driver.sh" long-double
