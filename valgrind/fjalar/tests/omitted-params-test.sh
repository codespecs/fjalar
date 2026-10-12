#!/bin/bash

# Tests that Fjalar omits a formal parameter whose location it cannot read,
# from both the .decls file and the .dtrace file.

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
# be position-independent.  -gno-variable-location-views keeps location view
# pairs out of the .debug_loc section.
gcc -gdwarf-4 -gno-variable-location-views -no-pie -O1 \
    -o "${output_dir}/omitted-params" "${test_dir}/omitted-params.c"

decls="${output_dir}/omitted-params.decls"
dtrace="${output_dir}/omitted-params.dtrace"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/omitted-params" \
              > "${output_dir}/omitted-params.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/omitted-params.out" >&2
  exit 1
fi

# One line per non-global variable declared at each program point other than
# main's:  "decls <ppt> <variable>", followed by one line per non-global
# variable at the first occurrence of each program point other than main's:
# "dtrace <ppt> <variable>".
actual="${output_dir}/omitted-params.actual"
awk '/^ppt / { ppt = $2 }
     /^  variable / { if ($2 !~ /^::/ && ppt !~ /^\.\.main\(/)
                        print "decls", ppt, $2 }' \
    "${decls}" > "${actual}"
awk '/^\.\.[a-z]*\(\):::/ { ppt = $0; getline; getline
                            if (ppt ~ /^\.\.main\(/ || seen[ppt]++) ppt = ""
                            next }
     ppt == "" { next }
     /^$/ { ppt = ""; next }
     { var = $0; getline; getline
       if (var !~ /^::/) print "dtrace", ppt, var }' \
    "${dtrace}" >> "${actual}"

if ! diff -u "${test_dir}/omitted-params.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from omitted-params.goal" >&2
  exit 1
fi

echo "$0: PASSED"
