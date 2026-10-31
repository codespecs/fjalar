#!/bin/bash

# Tests that Fjalar reads a formal parameter whose location is a location
# list, using the list's entry for the function's entry point.
#
# When optimized, C::m's this has a location list whose first entry is the
# register that holds it at the beginning of C::m.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

for tool in g++ readelf; do
  if ! command -v "${tool}" > /dev/null; then
    echo "$0: missing prerequisite: ${tool}" >&2
    exit 2
  fi
done

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

. "${test_dir}/environment-checks.sh"

# Fjalar does not read DWARF 5, and it recognizes a function's entry point
# only at the address in the debugging information, so the executable must not
# be position-independent.
g++ -gdwarf-4 -gno-variable-location-views -no-pie -O2 \
    -o "${output_dir}/param-location-list" "${test_dir}/param-location-list.cc"

# C::m's this must have a location list.
if ! readelf --debug-dump=info "${output_dir}/param-location-list" \
    | awk '/DW_TAG_/ { inparam = /DW_TAG_formal_parameter/; isthis = 0; next }
           inparam && /DW_AT_name.*: this$/ { isthis = 1; next }
           isthis && /DW_AT_location/ { found = /\(location list\)/; exit }
           END { exit !found }'; then
  unsuitable_environment "$0" "the location of C::m's this is not a location list"
fi

decls="${output_dir}/param-location-list.decls"
dtrace="${output_dir}/param-location-list.dtrace"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/param-location-list" \
              > "${output_dir}/param-location-list.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/param-location-list.out" >&2
  exit 1
fi

# One line per occurrence of this->x at C::m's program points:
# "<ppt> this->x <value>".
actual="${output_dir}/param-location-list.actual"
awk '/^C\.m\(int\):::/ { ppt = $0; next }
     /^$/ { ppt = ""; next }
     ppt != "" && $0 == "this->x" { getline; print ppt, "this->x", $0 }' \
    "${dtrace}" > "${actual}"

if ! diff -u "${test_dir}/param-location-list.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from param-location-list.goal" >&2
  exit 1
fi

echo "$0: PASSED"
