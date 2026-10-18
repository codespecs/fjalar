#!/bin/bash

# Tests that, under --dyncomp-interactions=none, DynComp does not make the
# operands of a comparison comparable when the comparison's result is
# computed by a condition-code helper such as amd64g_calculate_condition, nor
# the parts of a 64-bit or 128-bit load.
# In that mode, no operation is an interaction, so DynComp should merge no
# tags.  The expected comparability is in
# dyncomp-interactions-none.goal.

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
gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/dyncomp-interactions-none" \
    "${test_dir}/dyncomp-interactions-none.c"

# --vex-guest-chase=no ends each superblock at a jump, so that VEX cannot
# specialize the condition-code helper call into a comparison operation.
decls="${output_dir}/dyncomp-interactions-none.decls"
status=0
"${valgrind}" --tool=fjalar --vex-guest-chase=no \
              --dyncomp --dyncomp-interactions=none \
              --decls-only --decls-file="${decls}" \
              --trace-flags=01000000 --trace-notbelow=0 \
              "${output_dir}/dyncomp-interactions-none" \
              > "${output_dir}/dyncomp-interactions-none.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  tail -n 100 "${output_dir}/dyncomp-interactions-none.out" >&2
  exit 1
fi

# The trace contains the IR of each superblock, after the optimization that
# precedes instrumentation.  If VEX specialized the helper call into a
# comparison operation, then the test would not exercise DynComp's handling
# of helper calls.
if ! awk '/^==== SB / { inLess = ($0 ~ / less(\+[0-9]+)? /) }
          inLess && /g_calculate_condition\[/ { found = 1 }
          END { exit !found }' "${output_dir}/dyncomp-interactions-none.out"; then
  echo "$0: FAILED: the IR of less() does not call a calculate_condition helper" >&2
  # Show the IR of less(), or, if no superblock is in less(), the first
  # superblock headers, in case their format has changed.
  awk '/^==== SB / { inLess = ($0 ~ / less(\+[0-9]+)? /)
                     if (inLess) { found = 1 }
                     else if (++headers <= 10) { others = others $0 "\n" } }
       inLess { print }
       END { if (!found) printf "%s", others }' \
      "${output_dir}/dyncomp-interactions-none.out" >&2
  exit 1
fi

# One line per variable at each exit program point, other than main's:
# "<ppt> <variable> <comparability>".
actual="${output_dir}/dyncomp-interactions-none.comparability"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     /^    comparability / { if (ppt ~ /:::EXIT/ && ppt !~ /^\.\.main\(/)
                               print ppt, var, $2 }' "${decls}" > "${actual}"

if ! diff -u "${test_dir}/dyncomp-interactions-none.goal" "${actual}" >&2; then
  echo "$0: FAILED: comparability differs from dyncomp-interactions-none.goal" >&2
  exit 1
fi

echo "$0: PASSED"
