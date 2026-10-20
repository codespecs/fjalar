#!/bin/bash

# A positive control for dyncomp-interactions-none-test.sh:  in the default
# mode, the condition-code helper call in less() makes a and b comparable.
# Without this test, dyncomp-interactions-none-test.sh would pass even if
# helper calls never merged tags in any mode.  The expected comparability is
# in dyncomp-interactions-default.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" \
     --program=dyncomp-interactions-none dyncomp-interactions-default \
     '/^==== SB / { inLess = ($0 ~ / less(\+[0-9]+)? /) }
      inLess && /g_calculate_condition\[/ { found = 1 }
      END { exit !found }'
