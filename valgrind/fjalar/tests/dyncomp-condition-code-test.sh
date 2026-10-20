#!/bin/bash

# Tests that DynComp makes the operands of a comparison comparable when
# the comparison's result is computed by a condition-code helper such as
# amd64g_calculate_condition, with --dyncomp-approximate-literals.
#
# The arguments of the helper are (cond, cc_op, cc_dep1, cc_dep2, cc_ndep).
# The first argument is a constant condition code.  The helper's
# mc-exclusion mask excludes cond, cc_op, and cc_ndep, leaving the operands
# of the comparison, cc_dep1 and cc_dep2.  Under --dyncomp-approximate-literals,
# the tag of a constant is WEAK_FRESH_TAG, and merging a tag with
# WEAK_FRESH_TAG has no effect.  If DynComp merged each operand with that
# constant rather than with each other, the operands would not be
# comparable.  The expected comparability is in dyncomp-condition-code.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" \
     --program=dyncomp-interactions-none dyncomp-condition-code \
     '/^==== SB / { inLess = ($0 ~ / less(\+[0-9]+)? /) }
      inLess && /g_calculate_condition\[/ { found = 1 }
      END { exit !found }' \
     --dyncomp-approximate-literals
