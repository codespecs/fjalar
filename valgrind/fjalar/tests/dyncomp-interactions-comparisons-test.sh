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
# operands of a sub should not be comparable when its flags are preserved by
# an inc, whether via amd64g_calculate_rflags_c or, in the same basic block,
# via a CmpLT32U, or copied by a lahf via amd64g_calculate_rflags_all, or
# when a jnz reads the zero flag of the inc.  But they should be comparable
# when a setb reads the carry flag in the same basic block as an inc
# preserves it, or when a setb reads the carry flag that an inc preserved,
# whether the inc read it via a CmpLT32U or via amd64g_calculate_rflags_c,
# in the same basic block or a later one.
# The expected comparability is in dyncomp-interactions-comparisons.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" \
     dyncomp-interactions-comparisons \
     '/^==== SB / { fn = $0 }
      /g_calculate_condition\[/ { if (fn ~ / less(\+[0-9]+)? /) less = 1
                                  if (fn ~ / lessWide(\+[0-9]+)? /) wide = 1
                                  if (fn ~ / carry(\+[0-9]+)? /) carry = 1
                                  if (fn ~ / subIncJnz(\+[0-9]+)? /) jnz = 1
                                  if (fn ~ / subIncSetb(\+[0-9]+)? /) incSetb = 1
                                  if (fn ~ / subThenIncSetb(\+[0-9]+)? /) thenIncSetb = 1
                                  if (fn ~ / subIncSetbSameBlock(\+[0-9]+)? /) incSetbSame = 1 }
      /g_calculate_rflags_c\[/ { if (fn ~ / lessMask(\+[0-9]+)? /) mask = 1
                                 if (fn ~ / addWithCarry(\+[0-9]+)? /) adc = 1
                                 if (fn ~ / subThenInc(\+[0-9]+)? /) inc = 1
                                 if (fn ~ / subThenIncSetb(\+[0-9]+)? /) thenIncSetbC = 1 }
      /g_calculate_rflags_all\[/ { if (fn ~ / subThenLahf(\+[0-9]+)? /) lahf = 1 }
      /CmpLT32U\(/ { if (fn ~ / subThenIncSameBlock(\+[0-9]+)? /) incSame = 1
                     if (fn ~ / subSetbInc(\+[0-9]+)? /) setbInc = 1
                     if (fn ~ / subIncJnz(\+[0-9]+)? /) jnzC = 1
                     if (fn ~ / subIncSetb(\+[0-9]+)? /) incSetbC = 1
                     if (fn ~ / subIncSetbSameBlock(\+[0-9]+)? /) incSetbSameC = 1 }
      END { exit !(less && wide && carry && mask && adc && lahf && inc &&
                   incSame && setbInc && jnz && jnzC && incSetb && incSetbC &&
                   thenIncSetb && thenIncSetbC && incSetbSame &&
                   incSetbSameC) }' \
     --dyncomp-interactions=comparisons
