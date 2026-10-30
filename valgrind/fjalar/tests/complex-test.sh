#!/bin/bash

# Tests that Fjalar omits variables, struct members, formal parameters, and
# return values of _Complex types, which Daikon cannot represent, but
# reports a pointer to one, the other members of a struct, and the other
# formal parameters of a function.

exec "$(dirname "$0")/float-types-driver.sh" complex
