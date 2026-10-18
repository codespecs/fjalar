#!/bin/bash

# Tests that, under --dyncomp-interactions=none, DynComp does not make the
# operands of a comparison comparable when the comparison's result is
# computed by a condition-code helper such as amd64g_calculate_condition, nor
# the operand and result of an addition of a constant.
# In that mode, no operation is an interaction, so DynComp should merge no
# tags.  The expected comparability is in
# dyncomp-interactions-none.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" dyncomp-interactions-none \
     '/^==== SB / { inLess = ($0 ~ / less(\+[0-9]+)? /) }
      inLess && /g_calculate_condition\[/ { found = 1 }
      END { exit !found }' \
     --dyncomp-interactions=none
