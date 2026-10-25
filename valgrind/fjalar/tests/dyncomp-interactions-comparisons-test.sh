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
# operands of a sub should not be comparable when its flags are preserved by
# an inc, whether via amd64g_calculate_rflags_c or, in the same basic block,
# via a CmpLT32U, or copied by a lahf via amd64g_calculate_rflags_all, or
# when a jnz reads the zero flag of the inc.  But they should be comparable
# when a setb reads the carry flag in the same basic block as an inc
# preserves it, or when a setb reads the carry flag that an inc preserved,
# whether the inc read it via a CmpLT32U, via a CmpLT64U of the masked
# operands of a subb, or via amd64g_calculate_rflags_c, in the same basic
# block or a later one.  But they should not be comparable when the carry
# flag that a later inc preserves, which VEX computes as the constant 0, is
# that of a test.
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
                                  if (fn ~ / carry(\+[0-9]+)? /) carry = 1
                                  if (fn ~ / subIncJnz(\+[0-9]+)? /) jnz = 1
                                  if (fn ~ / subIncSetb(\+[0-9]+)? /) incSetb = 1
                                  if (fn ~ / subThenIncSetb(\+[0-9]+)? /) thenIncSetb = 1
                                  if (fn ~ / subIncSetbSameBlock(\+[0-9]+)? /) incSetbSame = 1
                                  if (fn ~ / subbIncSetb(\+[0-9]+)? /) subbSetb = 1
                                  if (fn ~ / subIncTestIncSetb(\+[0-9]+)? /) testSetb = 1 }
      /g_calculate_rflags_c\[/ { if (fn ~ / lessMask(\+[0-9]+)? /) mask = 1
                                 if (fn ~ / addWithCarry(\+[0-9]+)? /) adc = 1
                                 if (fn ~ / subThenInc(\+[0-9]+)? /) inc = 1
                                 if (fn ~ / subThenIncSetb(\+[0-9]+)? /) thenIncSetbC = 1
                                 if (fn ~ / subIncTestIncSetb(\+[0-9]+)? /) testC = 1 }
      /g_calculate_rflags_all\[/ { if (fn ~ / subThenLahf(\+[0-9]+)? /) lahf = 1 }
      /CmpLT32U\(/ { if (fn ~ / subThenIncSameBlock(\+[0-9]+)? /) incSame = 1
                     if (fn ~ / subSetbInc(\+[0-9]+)? /) setbInc = 1
                     if (fn ~ / subIncJnz(\+[0-9]+)? /) jnzC = 1
                     if (fn ~ / subIncSetb(\+[0-9]+)? /) incSetbC = 1
                     if (fn ~ / subIncSetbSameBlock(\+[0-9]+)? /) incSetbSameC = 1
                     if (fn ~ / subIncTestIncSetb(\+[0-9]+)? /) testCmp = 1 }
      /CmpLT64U\(/ { if (fn ~ / subbIncSetb(\+[0-9]+)? /) subbC = 1 }
      END { exit !(less && wide && wideSame && xorCmp && carry && mask && adc &&
                   lahf && inc && incSame && setbInc && jnz && jnzC && incSetb && incSetbC &&
                   thenIncSetb && thenIncSetbC && incSetbSame &&
                   incSetbSameC && subbSetb && subbC && testSetb && testCmp &&
                   !testC) }' \
     --dyncomp-interactions=comparisons
