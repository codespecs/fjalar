#!/bin/bash

# Tests that dyncomp_translate.c accounts for every IROp.
#
# typeOfPrimop (in VEX's ir_defs.c) gives each IROp's arity.  Each IROp
# must have a case label in the function for its arity (expr2tags_Unop_DC,
# expr2tags_Binop_DC, expr2tags_Triop_DC, or expr2tags_Qop_DC), or be
# listed in the comment of dyncomp_translate.c that begins "The following
# opcodes are not implemented", in the subsection whose heading names that
# function.  An IROp that is neither reaches approximate_unhandled_op_DC,
# which by default panics.  The comment's IROps are not used by the
# supported guests, amd64 and x86, so this test also checks that their
# front ends do not use any of them.
#
# The test fails after a VEX merge that adds an IROp, so that the new IROp
# gets an explicit tag behavior, and after a VEX merge that makes amd64 or
# x86 use a listed IROp.

# sort and comm must agree on the collating order.
export LC_ALL=C

fjalar="$(cd "$(dirname "$0")/.." && pwd)"
vex_priv="${fjalar}/../VEX/priv"
ir_defs="${vex_priv}/ir_defs.c"
dyncomp_translate="${fjalar}/kvasir/dyncomp_translate.c"
# The VEX source files that create IR for amd64 and x86 guests.
front_ends=("${vex_priv}"/guest_amd64_*.c "${vex_priv}"/guest_x86_*.c \
            "${vex_priv}"/guest_generic_*.c)

work_dir="$(mktemp -d)"
trap 'rm -rf "${work_dir}"' EXIT

status=0
fail() {
  echo "$0: FAILED: $1" >&2
  status=1
}

# Prints "<IROp> <arity>" for each IROp, according to typeOfPrimop, where
# <arity> is 1, 2, 3, or 4.  Each group of case labels ends with a statement
# such as UNARY(...) or BINARY(...).  TERNARY is a substring of QUATERNARY,
# and COMPARISON is a substring of UNARY_COMPARISON, so the longer names are
# tested first.
awk '
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
    if (line ~ /#/) { next }
    arity = 0
    if (line ~ /QUATERNARY *\(/) { arity = 4 }
    else if (line ~ /TERNARY *\(/) { arity = 3 }
    else if (line ~ /(UNARY|UNARY_COMPARISON) *\(/) { arity = 1 }
    else if (line ~ /(BINARY|COMPARISON) *\(/) { arity = 2 }
    if (arity != 0) {
      n = split(labels, ops, " ")
      for (i = 1; i <= n; i++) print ops[i], arity
      labels = ""
    }
  }' "$ir_defs" | sort -u > "${work_dir}/arities"

# The IROps that the front ends use.
grep -ohw 'Iop_[A-Za-z0-9_]*' "${front_ends[@]}" | sort -u > "${work_dir}/front-end"

# The IROps listed in the subsection of the "not implemented" comment whose
# heading names expr2tags_<name>_DC, for each name.  Writes one file per
# subsection, named listed-<name>.
awk -v dir="${work_dir}" '
  /^ \* The following opcodes are not implemented/ { incomment = 1 }
  !incomment { next }
  /^ \*\// { exit }
  match($0, /cases belong in expr2tags_[A-Za-z]+_DC/) {
    name = substr($0, RSTART, RLENGTH)
    sub(/.*expr2tags_/, "", name); sub(/_DC$/, "", name)
    out = dir "/listed-" name
    printf "" > out
    next
  }
  out != "" && match($0, /case +Iop_[A-Za-z0-9_]+ *:/) {
    label = substr($0, RSTART, RLENGTH)
    sub(/case +/, "", label); sub(/ *:$/, "", label)
    print label > out
  }' "$dyncomp_translate"

for name_arity in Unop:1 Binop:2 Triop:3 Qop:4; do
  name="${name_arity%:*}"
  arity="${name_arity#*:}"
  fn="expr2tags_${name}_DC"

  awk -v arity="$arity" '$2 == arity { print $1 }' "${work_dir}/arities" \
    > "${work_dir}/ops"

  # The IROps that fn has a case label for.  A case label that falls
  # through directly to the default case is not handled; it is reported.
  awk -v fallthrough="${work_dir}/fallthrough" '
    $0 ~ "^IR(Expr|Atom)\\* '"$fn"' *\\(" { infn = 1 }
    infn && /^}/ { exit }
    !infn { next }
    {
      sub(/\/\/.*/, "")
      if ($0 ~ /^[ \t]*$/) { next }
      if ($0 ~ /^[ \t]*default *:/) {
        for (op in pending) print op > fallthrough
      }
      delete pending
      while (match($0, /case +Iop_[A-Za-z0-9_]+ *:/)) {
        label = substr($0, RSTART, RLENGTH)
        sub(/case +/, "", label); sub(/ *:$/, "", label)
        print label
        pending[label] = 1
        $0 = substr($0, RSTART + RLENGTH)
      }
      if ($0 !~ /^[ \t]*$/) { delete pending }
    }' "$dyncomp_translate" | sort -u > "${work_dir}/handled"

  if [ "$name" = Unop ]; then
    : > "${work_dir}/listed"
  elif [ -f "${work_dir}/listed-${name}" ]; then
    sort -u "${work_dir}/listed-${name}" > "${work_dir}/listed"
  else
    fail "the comment that lists the IROps that DynComp does not implement has no subsection for ${fn}"
    continue
  fi

  if [ ! -s "${work_dir}/ops" ] || [ ! -s "${work_dir}/handled" ]; then
    fail "could not parse ${ir_defs} or ${fn} in ${dyncomp_translate}"
    continue
  fi

  sort -u "${work_dir}/handled" "${work_dir}/listed" > "${work_dir}/accounted"
  missing=$(comm -23 "${work_dir}/ops" "${work_dir}/accounted")
  if [ -n "$missing" ]; then
    fail "${fn} has no case for, and the comment does not list, these IROps of arity ${arity}:
${missing}"
  fi
  extra=$(comm -13 "${work_dir}/ops" "${work_dir}/handled")
  if [ -n "$extra" ]; then
    fail "${fn} has a case for these IROps, which do not have arity ${arity}:
${extra}"
  fi
  extra=$(comm -13 "${work_dir}/ops" "${work_dir}/listed")
  if [ -n "$extra" ]; then
    fail "the comment lists, under ${fn}, these IROps, which do not exist or do not have arity ${arity}:
${extra}"
  fi
  both=$(comm -12 "${work_dir}/handled" "${work_dir}/listed")
  if [ -n "$both" ]; then
    fail "${fn} has a case for these IROps, which the comment also lists:
${both}"
  fi
  if [ -s "${work_dir}/fallthrough" ]; then
    fail "in ${fn}, these case labels fall through to the default case; give them a tag behavior, or list them in the comment instead:
$(sort -u "${work_dir}/fallthrough")"
    rm -f "${work_dir}/fallthrough"
  fi
  used=$(comm -12 "${work_dir}/listed" "${work_dir}/front-end")
  if [ -n "$used" ]; then
    fail "the comment lists, under ${fn}, these IROps, which the amd64 or x86 front end uses:
${used}"
  fi
done

exit $status
