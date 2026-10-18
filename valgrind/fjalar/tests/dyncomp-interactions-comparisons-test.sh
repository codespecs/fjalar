#!/bin/bash

# Tests that, under --dyncomp-interactions=comparisons, DynComp merges the
# tags of a helper call's arguments only if the helper reads flags that a
# comparison set.  The operands of a cmp should be comparable when its flags
# are read via amd64g_calculate_condition (setl) or amd64g_calculate_rflags_c
# (sbb), and so should the high halves of two 128-bit integers that are
# compared with cmp, sbb, and setl (but they are not; the .goal file
# records that known limitation, which is explained at lessWide()).  The
# operands of an add should not be comparable when its flags are read via
# amd64g_calculate_condition (setc) or amd64g_calculate_rflags_c (adc).  The
# operands of a sub should not be comparable when its flags are copied by a
# lahf via amd64g_calculate_rflags_all.
# The expected comparability is in dyncomp-interactions-comparisons.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" \
     dyncomp-interactions-comparisons \
     '/^==== SB / { fn = $0 }
      /g_calculate_condition\[/ { if (fn ~ / less(\+[0-9]+)? /) less = 1
                                  if (fn ~ / lessWide(\+[0-9]+)? /) wide = 1
                                  if (fn ~ / carry(\+[0-9]+)? /) carry = 1 }
      /g_calculate_rflags_c\[/ { if (fn ~ / lessMask(\+[0-9]+)? /) mask = 1
                                 if (fn ~ / addWithCarry(\+[0-9]+)? /) adc = 1 }
      /g_calculate_rflags_all\[/ { if (fn ~ / subThenLahf(\+[0-9]+)? /) lahf = 1 }
      END { exit !(less && wide && carry && mask && adc && lahf) }' \
     --dyncomp-interactions=comparisons
