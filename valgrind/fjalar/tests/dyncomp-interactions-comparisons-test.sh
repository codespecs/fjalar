#!/bin/bash

# Tests that, under --dyncomp-interactions=comparisons, DynComp merges the
# tags of a helper call's arguments only if the helper reads flags that a
# comparison set.  The operands of a cmp should be comparable when its flags
# are read via amd64g_calculate_condition (setl) or amd64g_calculate_rflags_c
# (sbb), and so should the high halves of two 128-bit integers that are
# compared with cmp, sbb, and setl, whether or not the sbb and the setl are in
# the same basic block.  The operands of an xor that precedes a cmp should not
# be comparable with the other operand of the cmp.  The operands of an add
# should not be comparable when its flags are read via
# amd64g_calculate_condition (setc) or amd64g_calculate_rflags_c (adc).  The
# operands of a sub should not be comparable when its flags are copied by a
# lahf via amd64g_calculate_rflags_all.
# The expected comparability is in dyncomp-interactions-comparisons.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" \
     dyncomp-interactions-comparisons \
     '/^==== SB / { fn = $0 }
      /g_calculate_condition\[/ { if (fn ~ / less(\+[0-9]+)? /) less = 1
                                  if (fn ~ / lessWide(\+[0-9]+)? /) wide = 1
                                  # CC_OP is a constant, so the sbb is in
                                  # the same superblock.
                                  if (fn ~ / lessWideSameBlock(\+[0-9]+)? / \
                                      && /\(0x[0-9A-F]+:I64,0x[0-9A-F]+:I64,/) wideSame = 1
                                  if (fn ~ / xorThenLess(\+[0-9]+)? /) xorCmp = 1
                                  if (fn ~ / carry(\+[0-9]+)? /) carry = 1 }
      /g_calculate_rflags_c\[/ { if (fn ~ / lessMask(\+[0-9]+)? /) mask = 1
                                 if (fn ~ / addWithCarry(\+[0-9]+)? /) adc = 1 }
      /g_calculate_rflags_all\[/ { if (fn ~ / subThenLahf(\+[0-9]+)? /) lahf = 1 }
      END { exit !(less && wide && wideSame && xorCmp && carry && mask && adc && lahf) }' \
     --dyncomp-interactions=comparisons
