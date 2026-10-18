#!/bin/bash

# Tests that, under --dyncomp-interactions=units, DynComp merges the tags of
# the arguments of a helper call that reads flags only if a comparison set
# the flags, and merges the tags of the arguments of other helper calls.  The
# operands of a cmp should be comparable when its flags are read via
# amd64g_calculate_condition (setl).  The operands of an imul should not be
# comparable when its flags are read via amd64g_calculate_condition (seto).
# The operands of a psadbw (via amd64g_calculate_mmx_psadbw) should be
# comparable.
# The expected comparability is in dyncomp-interactions-units.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" \
     dyncomp-interactions-units \
     '/^==== SB / { fn = $0 }
      /g_calculate_condition\[/ { if (fn ~ / less(\+[0-9]+)? /) less = 1
                                  if (fn ~ / overflow(\+[0-9]+)? /) ovf = 1 }
      /g_calculate_mmx_psadbw[{]/ { if (fn ~ / absDiffSum(\+[0-9]+)? /) psadbw = 1 }
      END { exit !(less && ovf && psadbw) }' \
     --dyncomp-interactions=units
