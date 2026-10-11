#!/bin/bash

# Tests that Fjalar reads the .debug_loc section of an optimized program.
#
# For optimized code, GCC emits location view pairs (DW_AT_GNU_locviews) in
# the .debug_loc section, before the location lists.  If Fjalar reads the
# section as a sequence of location lists, it misreads the location view
# pairs as location list entries and loops forever.
#
# The test checks that Fjalar terminates without warnings and that it reads
# the same location list entries as readelf does.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

for tool in gcc readelf timeout; do
  if ! command -v "${tool}" > /dev/null; then
    echo "$0: missing prerequisite: ${tool}" >&2
    exit 2
  fi
done

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

# Prints one line per location list entry in the .debug_loc section:  the
# entry's offset and its begin and end addresses, or "end" for the end of a
# list.  The input is the output of "readelf --debug-dump=loc" or of
# "valgrind --tool=fjalar --fjalar-debug-dump".  readelf prints an entry that
# has views on two lines, and it prints the location view pairs, which are
# not entries.
loc_list_entries() {
  awk '
    /^Contents of the .debug_loc section:/ { in_loc = 1; next }
    /^Contents of / { in_loc = 0 }
    !in_loc { next }
    have_views { print offset, $1, $2; have_views = 0; next }
    $2 == "<End" { print $1, "end"; next }
    / views at / { offset = $1; have_views = 1; next }
    $1 ~ /^[0-9a-f]+$/ && $2 ~ /^[0-9a-f]+$/ && $3 ~ /^[0-9a-f]+$/ { print $1, $2, $3 }
  ' "$1" | sort -u
}

for opt in -O1 -O2; do
  # Fjalar does not read DWARF 5, and it recognizes a function's entry point
  # only at the address in the debugging information, so the executable must
  # not be position-independent.  -gvariable-location-views is the default
  # for optimized code; it is explicit here in case the default changes.
  gcc -gdwarf-4 -gvariable-location-views -no-pie "${opt}" \
      -o "${output_dir}/location-views" "${test_dir}/location-views.c"

  readelf_out="${output_dir}/location-views${opt}.readelf"
  readelf --debug-dump=loc "${output_dir}/location-views" > "${readelf_out}"
  if ! grep -q 'location view pair' "${readelf_out}"; then
    echo "$0: FAILED (${opt}): gcc emitted no location views" >&2
    cat "${readelf_out}" >&2
    exit 1
  fi

  out="${output_dir}/location-views${opt}.out"
  dtrace="${output_dir}/location-views${opt}.dtrace"
  status=0
  timeout 120 "${valgrind}" --tool=fjalar --fjalar-debug-dump \
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

  if grep -q 'Warning:' "${out}"; then
    echo "$0: FAILED (${opt}): Fjalar issued a warning" >&2
    grep 'Warning:' "${out}" >&2
    exit 1
  fi

  loc_list_entries "${readelf_out}" > "${output_dir}/expected-entries"
  loc_list_entries "${out}" > "${output_dir}/actual-entries"
  if [ ! -s "${output_dir}/expected-entries" ]; then
    echo "$0: FAILED (${opt}): readelf printed no location list entries" >&2
    exit 1
  fi
  if ! diff "${output_dir}/expected-entries" "${output_dir}/actual-entries" >&2; then
    echo "$0: FAILED (${opt}): Fjalar and readelf read different location list entries" >&2
    exit 1
  fi

  if ! grep -q '^\.\.observe():::EXIT' "${dtrace}"; then
    echo "$0: FAILED (${opt}): no exit program point for observe() in ${dtrace}" >&2
    cat "${out}" >&2
    exit 1
  fi
done

echo "$0: PASSED"
