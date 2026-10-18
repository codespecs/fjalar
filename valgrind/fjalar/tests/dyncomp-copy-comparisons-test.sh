#!/bin/bash

# Tests that, under --dyncomp-interactions=comparisons, a 64-bit or 128-bit
# load does not make the fields it reads comparable.  In that mode, only
# comparisons are interactions.  The expected
# comparability is in dyncomp-copy-comparisons.goal.

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
gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/dyncomp-copy-comparisons" \
    "${test_dir}/dyncomp-copy-comparisons.c"

decls="${output_dir}/dyncomp-copy-comparisons.decls"
status=0
"${valgrind}" --tool=fjalar --dyncomp --dyncomp-interactions=comparisons \
              --decls-only --decls-file="${decls}" \
              "${output_dir}/dyncomp-copy-comparisons" \
              > "${output_dir}/dyncomp-copy-comparisons.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  tail -n 100 "${output_dir}/dyncomp-copy-comparisons.out" >&2
  exit 1
fi

# One line per variable at each exit program point, other than main's:
# "<ppt> <variable> <comparability>".
actual="${output_dir}/dyncomp-copy-comparisons.comparability"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     /^    comparability / { if (ppt ~ /:::EXIT/ && ppt !~ /^\.\.main\(/)
                               print ppt, var, $2 }' "${decls}" > "${actual}"

if ! diff -u "${test_dir}/dyncomp-copy-comparisons.goal" "${actual}" >&2; then
  echo "$0: FAILED: comparability differs from dyncomp-copy-comparisons.goal" >&2
  exit 1
fi

echo "$0: PASSED"
