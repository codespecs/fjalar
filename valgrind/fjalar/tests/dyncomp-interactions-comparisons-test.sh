#!/bin/bash

# Tests that, under --dyncomp-interactions=comparisons, DynComp merges the
# tags of a helper call's arguments only if the helper evaluates a
# condition.  The operands of a comparison whose result is computed by
# amd64g_calculate_condition should be comparable; the operands of an
# addition whose carry is computed by amd64g_calculate_rflags_c should not.
# The expected comparability is in dyncomp-interactions-comparisons.goal.

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
gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/dyncomp-interactions-comparisons" \
    "${test_dir}/dyncomp-interactions-comparisons.c"

# --vex-guest-chase=no ends each superblock at a jump, so that VEX cannot
# specialize the helper calls into IR operations.
fjalar_args=(--tool=fjalar --vex-guest-chase=no
             --dyncomp --dyncomp-interactions=comparisons)

# The trace contains the IR of each superblock, after the optimization that
# precedes instrumentation.  If VEX specialized a helper call, then the test
# would not exercise DynComp's handling of helper calls.  The trace is large,
# so it is filtered rather than saved, and the comparability is computed by a
# separate run without tracing.
if ! "${valgrind}" "${fjalar_args[@]}" --decls-only \
                   --decls-file="${output_dir}/trace.decls" \
                   --trace-flags=01000000 --trace-notbelow=0 \
                   "${output_dir}/dyncomp-interactions-comparisons" 2>&1 \
     | awk '/^==== SB / { inLess = ($0 ~ / less(\+[0-9]+)? /)
                          inAdd = ($0 ~ / addWithCarry(\+[0-9]+)? /) }
            inLess && /g_calculate_condition\[/ { foundCondition = 1 }
            inAdd && /g_calculate_rflags_c\[/ { foundCarry = 1 }
            END { exit !(foundCondition && foundCarry) }'; then
  echo "$0: FAILED: the IR of less() does not call a calculate_condition helper, or the IR of addWithCarry() does not call a calculate_rflags_c helper" >&2
  exit 1
fi

decls="${output_dir}/dyncomp-interactions-comparisons.decls"
status=0
"${valgrind}" "${fjalar_args[@]}" --decls-only --decls-file="${decls}" \
              "${output_dir}/dyncomp-interactions-comparisons" \
              > "${output_dir}/dyncomp-interactions-comparisons.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  tail -n 100 "${output_dir}/dyncomp-interactions-comparisons.out" >&2
  exit 1
fi

# One line per variable at each exit program point, other than main's:
# "<ppt> <variable> <comparability>".
actual="${output_dir}/dyncomp-interactions-comparisons.comparability"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     /^    comparability / { if (ppt ~ /:::EXIT/ && ppt !~ /^\.\.main\(/)
                               print ppt, var, $2 }' "${decls}" > "${actual}"

if ! diff -u "${test_dir}/dyncomp-interactions-comparisons.goal" "${actual}" >&2; then
  echo "$0: FAILED: comparability differs from dyncomp-interactions-comparisons.goal" >&2
  exit 1
fi

echo "$0: PASSED"
