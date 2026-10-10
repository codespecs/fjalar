#!/bin/bash

# Tests that Fjalar reads the .debug_loc section of an optimized program.
#
# For optimized code, GCC emits location view pairs (DW_AT_GNU_locviews) in
# the .debug_loc section, before the location lists.  If Fjalar reads the
# section as a sequence of location lists, it misreads the location view
# pairs as location list entries and loops forever.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

for opt in -O1 -O2; do
  # Fjalar does not read DWARF 5, and it recognizes a function's entry point
  # only at the address in the debugging information, so the executable must
  # not be position-independent.  -gvariable-location-views is the default
  # for optimized code; it is explicit here in case the default changes.
  gcc -gdwarf-4 -gvariable-location-views -no-pie "${opt}" \
      -o "${output_dir}/location-views" "${test_dir}/location-views.c"

  out="${output_dir}/location-views${opt}.out"
  dtrace="${output_dir}/location-views${opt}.dtrace"
  status=0
  timeout 120 "${valgrind}" --tool=fjalar \
                --decls-file="${output_dir}/location-views${opt}.decls" \
                --dtrace-file="${dtrace}" \
                "${output_dir}/location-views" > "${out}" 2>&1 || status=$?

  if [ "${status}" -eq 124 ]; then
    echo "$0: FAILED (${opt}): Fjalar did not terminate" >&2
    tail -n 20 "${out}" >&2
    exit 1
  fi
  if [ "${status}" -ne 0 ]; then
    echo "$0: FAILED (${opt}): Fjalar exited with status ${status}" >&2
    cat "${out}" >&2
    exit 1
  fi

  if grep -q 'loc lists\|Location list' "${out}"; then
    echo "$0: FAILED (${opt}): Fjalar warned about location lists" >&2
    cat "${out}" >&2
    exit 1
  fi

  if ! grep -q '^\.\.observe():::EXIT' "${dtrace}"; then
    echo "$0: FAILED (${opt}): no exit program point for observe() in ${dtrace}" >&2
    cat "${out}" >&2
    exit 1
  fi
done

echo "$0: PASSED"
