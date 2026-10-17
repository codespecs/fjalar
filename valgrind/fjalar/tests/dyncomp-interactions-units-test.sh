#!/bin/bash

# Tests that, under --dyncomp-interactions=units, DynComp merges the tags of
# a helper call's arguments only if the helper reads flags that a comparison
# set.  The operands of a cmp should be comparable when its flags are read via
# amd64g_calculate_condition (setl).  The operands of an imul should not be
# comparable when its flags are read via amd64g_calculate_condition (seto).
# The expected comparability is in dyncomp-interactions-units.goal.

exec "$(dirname "$0")/dyncomp-comparability-test.sh" \
     dyncomp-interactions-units \
     '/^==== SB / { fn = $0 }
      /g_calculate_condition\[/ { if (fn ~ / less(\+[0-9]+)? /) less = 1
                                  if (fn ~ / overflow(\+[0-9]+)? /) ovf = 1 }
      END { exit !(less && ovf) }' \
     --dyncomp-interactions=units
