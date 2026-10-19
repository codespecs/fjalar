#!/bin/bash

# Tests DynComp's comparability:  whether the variables at each exit
# program point are comparable to each other.  The expected comparability is
# in dyncomp-comparability.goal, under both --dyncomp-interactions=all and
# --dyncomp-interactions=units.

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
gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/dyncomp-comparability" \
    "${test_dir}/dyncomp-comparability.c"

for interactions in all units; do
  decls="${output_dir}/dyncomp-comparability.decls"
  status=0
  "${valgrind}" --tool=fjalar --dyncomp \
                --dyncomp-interactions="${interactions}" \
                --decls-only --decls-file="${decls}" \
                "${output_dir}/dyncomp-comparability" \
                > "${output_dir}/dyncomp-comparability.out" 2>&1 || status=$?

  if [ "${status}" -ne 0 ]; then
    echo "$0: FAILED: under --dyncomp-interactions=${interactions}," \
         "Fjalar exited with status ${status}" >&2
    cat "${output_dir}/dyncomp-comparability.out" >&2
    exit 1
  fi

  # One line per variable at each exit program point, other than main's:
  # "<ppt> <variable> <comparability>".
  actual="${output_dir}/dyncomp-comparability.comparability"
  awk '/^ppt / { ppt = $2 }
       /^  variable / { var = $2 }
       /^    comparability / { if (ppt ~ /:::EXIT/ && ppt !~ /^\.\.main\(/)
                                 print ppt, var, $2 }' "${decls}" > "${actual}"

  if ! diff -u "${test_dir}/dyncomp-comparability.goal" "${actual}" >&2; then
    echo "$0: FAILED: under --dyncomp-interactions=${interactions}," \
         "comparability differs from dyncomp-comparability.goal" >&2
    exit 1
  fi
done

echo "$0: PASSED"
