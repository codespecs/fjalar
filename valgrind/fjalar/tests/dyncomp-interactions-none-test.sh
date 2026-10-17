#!/bin/bash

# Tests that, under --dyncomp-interactions=none, DynComp does not make the
# operands of a comparison comparable when the comparison's result is
# computed by a condition-code helper such as amd64g_calculate_condition, nor
# the two halves of a 128-bit load, nor the two fields of a struct copied by
# a 64-bit load.
# In that mode, no operation is an interaction, so DynComp should merge no
# tags.  The expected comparability is in
# dyncomp-interactions-none.goal.

exec "$(dirname "$0")/dyncomp-comparability-test.sh" dyncomp-interactions-none \
     '/^==== SB / { inLess = ($0 ~ / less(\+[0-9]+)? /) }
      inLess && /g_calculate_condition\[/ { found = 1 }
      END { exit !found }' \
     --dyncomp-interactions=none
