#!/bin/bash

# Tests that Fjalar reports a returned double as uninitialized if any of its
# 8 bytes is uninitialized.
#
# On amd64, a double is returned in the low 8 bytes of XMM0.  Fjalar must copy
# the V-bits of all 8 bytes, not only of the low 4.

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
gcc -gdwarf-4 -no-pie -o "${output_dir}/double-return-shadow" \
    "${test_dir}/double-return-shadow.c"

dtrace="${output_dir}/double-return-shadow.dtrace"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${output_dir}/double-return-shadow.decls" \
              --dtrace-file="${dtrace}" \
              "${output_dir}/double-return-shadow" \
              > "${output_dir}/double-return-shadow.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/double-return-shadow.out" >&2
  exit 1
fi

# One line per return value of a function other than main:
# "<ppt> <value> <modbit>".
actual="${output_dir}/double-return-shadow.actual"
awk '/^\.\.[a-z_]*\(\):::EXIT/ { ppt = ($0 ~ /^\.\.main\(/) ? "" : $0; next }
     /^$/ { ppt = ""; next }
     ppt != "" && $0 == "return" { getline value; getline modbit
                                   print ppt, value, modbit }' \
    "${dtrace}" > "${actual}"

if ! diff -u "${test_dir}/double-return-shadow.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from double-return-shadow.goal" >&2
  exit 1
fi

echo "$0: PASSED"
