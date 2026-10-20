#!/bin/bash

# Tests that expr2tags_Unop_DC in dyncomp_translate.c has a case label for
# exactly the unary IROps, which are the IROps that typeOfPrimop (in VEX's
# ir_defs.c) types with UNARY or UNARY_COMPARISON.  A unary IROp without a
# case label reaches approximate_unhandled_op_DC, which by default panics.
# This test fails after a VEX merge that adds a unary IROp, so that the new
# IROp gets an explicit tag behavior.

# sort and comm must agree on the collating order.
export LC_ALL=C

fjalar="$(cd "$(dirname "$0")/.." && pwd)"
ir_defs="${fjalar}/../VEX/priv/ir_defs.c"
dyncomp_translate="${fjalar}/kvasir/dyncomp_translate.c"

# The unary IROps, according to typeOfPrimop.  Each group of case labels
# ends with a statement such as UNARY(...) or BINARY(...).
unary_ops=$(awk '
  /^void typeOfPrimop *\(/ { infn = 1 }
  infn && /^}/ { exit }
  !infn { next }
  {
    line = $0
    while (match(line, /case +Iop_[A-Za-z0-9_]+ *:/)) {
      label = substr(line, RSTART, RLENGTH)
      sub(/case +/, "", label); sub(/ *:$/, "", label)
      labels = labels " " label
      line = substr(line, RSTART + RLENGTH)
    }
    if (line ~ /(UNARY|UNARY_COMPARISON) *\(/ && line !~ /#/) {
      n = split(labels, ops, " ")
      for (i = 1; i <= n; i++) print ops[i]
      labels = ""
    } else if (line ~ /(BINARY|TERNARY|QUATERNARY|COMPARISON) *\(/ && line !~ /#/) {
      labels = ""
    }
  }' "$ir_defs" | sort -u)

# The IROps that expr2tags_Unop_DC has a case label for.
handled_ops=$(awk '
  /^IRExpr\* expr2tags_Unop_DC *\(/ { infn = 1 }
  infn && /^}/ { exit }
  infn {
    sub(/\/\/.*/, "")
    while (match($0, /case +Iop_[A-Za-z0-9_]+ *:/)) {
      label = substr($0, RSTART, RLENGTH)
      sub(/case +/, "", label); sub(/ *:$/, "", label)
      print label
      $0 = substr($0, RSTART + RLENGTH)
    }
  }' "$dyncomp_translate" | sort -u)

if [ -z "$unary_ops" ] || [ -z "$handled_ops" ]; then
  echo "$0: FAILED: could not parse $ir_defs or $dyncomp_translate" >&2
  exit 1
fi

missing=$(comm -23 <(echo "$unary_ops") <(echo "$handled_ops"))
extra=$(comm -13 <(echo "$unary_ops") <(echo "$handled_ops"))

status=0
if [ -n "$missing" ]; then
  echo "$0: FAILED: expr2tags_Unop_DC has no case for these unary IROps:" >&2
  echo "$missing" >&2
  status=1
fi
if [ -n "$extra" ]; then
  echo "$0: FAILED: expr2tags_Unop_DC has a case for these non-unary IROps:" >&2
  echo "$extra" >&2
  status=1
fi
exit $status
