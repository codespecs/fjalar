#!/bin/bash

# Tests that DynComp makes the operands of a comparison comparable when
# the comparison's result is computed by a condition-code helper such as
# amd64g_calculate_condition, with --dyncomp-approximate-literals.
#
# The arguments of the helper are (cond, cc_op, cc_dep1, cc_dep2, cc_ndep).
# The first argument is a constant condition code.  The helper's
# mc-exclusion mask excludes cond, cc_op, and cc_ndep, leaving the operands
# of the comparison, cc_dep1 and cc_dep2.  Under --dyncomp-approximate-literals,
# the tag of a constant is WEAK_FRESH_TAG, and merging a tag with
# WEAK_FRESH_TAG has no effect.  If DynComp merged each operand with that
# constant rather than with each other, the operands would not be
# comparable.  The expected comparability is in dyncomp-condition-code.goal.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

# Fjalar does not read DWARF 5, and it recognizes a function's entry point
# only at the address in the debugging information, so the executable must not
# be position-independent.
gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/dyncomp-condition-code" \
    "${test_dir}/dyncomp-condition-code.c"

# --vex-guest-chase=no ends each superblock at a jump, so that VEX cannot
# specialize the condition-code helper call into a comparison operation.
fjalar_args=(--tool=fjalar --vex-guest-chase=no
             --dyncomp --dyncomp-approximate-literals)

# The trace contains the IR of each superblock, after the optimization that
# precedes instrumentation.  If VEX specialized the helper call into a
# comparison operation, then the test would not exercise DynComp's handling
# of helper calls.  The trace is large, so it is filtered rather than saved,
# and the comparability is computed by a separate run without tracing.
if ! "${valgrind}" "${fjalar_args[@]}" --decls-only \
                   --decls-file="${output_dir}/trace.decls" \
                   --trace-flags=01000000 --trace-notbelow=0 \
                   "${output_dir}/dyncomp-condition-code" 2>&1 \
     | awk '/^==== SB / { inLess = ($0 ~ / less(\+[0-9]+)? /) }
            inLess && /g_calculate_condition\[/ { found = 1 }
            END { exit !found }'; then
  echo "$0: FAILED: the IR of less() does not call a calculate_condition helper" >&2
  exit 1
fi

decls="${output_dir}/dyncomp-condition-code.decls"
status=0
"${valgrind}" "${fjalar_args[@]}" --decls-only --decls-file="${decls}" \
              "${output_dir}/dyncomp-condition-code" \
              > "${output_dir}/dyncomp-condition-code.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  tail -n 100 "${output_dir}/dyncomp-condition-code.out" >&2
  exit 1
fi

# One line per variable at each exit program point, other than main's:
# "<ppt> <variable> <comparability>".
actual="${output_dir}/dyncomp-condition-code.comparability"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     /^    comparability / { if (ppt ~ /:::EXIT/ && ppt !~ /^\.\.main\(/)
                               print ppt, var, $2 }' "${decls}" > "${actual}"

if ! diff -u "${test_dir}/dyncomp-condition-code.goal" "${actual}" >&2; then
  echo "$0: FAILED: comparability differs from dyncomp-condition-code.goal" >&2
  exit 1
fi

echo "$0: PASSED"
