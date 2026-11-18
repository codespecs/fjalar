#!/bin/bash

# Tests that Fjalar computes the frame base of a function whose frame base is
# a location list, using the list's entry for the function's entry point.
#
# Strict DWARF 2 has no DW_OP_call_frame_cfa, so GCC describes each
# function's frame base as a location list.  The locations of f's formal
# parameters are offsets from the frame base, so Fjalar reads them correctly
# only if it computes the frame base correctly.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

for tool in gcc readelf; do
  if ! command -v "${tool}" > /dev/null; then
    echo "$0: missing prerequisite: ${tool}" >&2
    exit 2
  fi
done

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

. "${test_dir}/environment-checks.sh"

# Fjalar recognizes a function's entry point only at the address in the
# debugging information, so the executable must not be position-independent.
gcc -gdwarf-2 -gstrict-dwarf -no-pie -O0 \
    -o "${output_dir}/frame-base-location-list" "${test_dir}/frame-base-location-list.c"

# f's frame base must be a location list.
if ! readelf --debug-dump=info "${output_dir}/frame-base-location-list" \
    | awk '/DW_TAG_/ { insub = /DW_TAG_subprogram/; isf = 0; next }
           insub && /DW_AT_name.*: f$/ { isf = 1; next }
           isf && /DW_AT_frame_base/ { found = /\(location list\)/; exit }
           END { exit !found }'; then
  unsuitable_environment "$0" "the frame base of f is not a location list"
fi

decls="${output_dir}/frame-base-location-list.decls"
dtrace="${output_dir}/frame-base-location-list.dtrace"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/frame-base-location-list" \
              > "${output_dir}/frame-base-location-list.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/frame-base-location-list.out" >&2
  exit 1
fi

# One line per formal parameter at f's program points:
# "<ppt> <parameter> <value>".
actual="${output_dir}/frame-base-location-list.actual"
awk '/^\.\.f\(\):::/ { ppt = $0; next }
     /^$/ { ppt = ""; next }
     ppt != "" && ($0 == "a" || $0 == "b") { name = $0; getline; print ppt, name, $0 }' \
    "${dtrace}" > "${actual}"

if ! diff -u "${test_dir}/frame-base-location-list.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from frame-base-location-list.goal" >&2
  exit 1
fi

echo "$0: PASSED"
