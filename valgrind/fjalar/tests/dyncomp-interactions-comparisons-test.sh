#!/bin/bash

# Tests that, under --dyncomp-interactions=comparisons, DynComp merges the
# tags of a helper call's arguments only if the helper reads flags that a
# comparison set.  The operands of a cmp should be comparable when its flags
# are read via amd64g_calculate_condition (setl) or amd64g_calculate_rflags_c
# (sbb).  The operands of an add should not be comparable when its flags are
# read via amd64g_calculate_condition (setc) or amd64g_calculate_rflags_c
# (adc).  Nor should the two halves of a 128-bit load, nor the two fields of
# a struct copied by a 64-bit load.
# The expected comparability is in dyncomp-interactions-comparisons.goal.

exec "$(dirname "$0")/dyncomp-comparability-test.sh" \
     dyncomp-interactions-comparisons \
     '/^==== SB / { fn = $0 }
      /g_calculate_condition\[/ { if (fn ~ / less(\+[0-9]+)? /) less = 1
                                  if (fn ~ / carry(\+[0-9]+)? /) carry = 1 }
      /g_calculate_rflags_c\[/ { if (fn ~ / lessMask(\+[0-9]+)? /) mask = 1
                                 if (fn ~ / addWithCarry(\+[0-9]+)? /) adc = 1 }
      END { exit !(less && carry && mask && adc) }' \
     --dyncomp-interactions=comparisons
