#!/bin/bash

# Tests that Fjalar reports the fields of a returned struct.
#
# On amd64, a struct of at most 16 bytes is returned in RAX and RDX, and a
# larger struct is returned in memory, at the address in RAX.

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
gcc -gdwarf-4 -no-pie -o "${output_dir}/small-struct-return" \
    "${test_dir}/small-struct-return.c"

dtrace="${output_dir}/small-struct-return.dtrace"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${output_dir}/small-struct-return.decls" \
              --dtrace-file="${dtrace}" \
              "${output_dir}/small-struct-return" \
              > "${output_dir}/small-struct-return.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/small-struct-return.out" >&2
  exit 1
fi

# One line per variable derived from the return value of a function other than
# main: "<ppt> <variable> <value> <modbit>".  The value of a struct is its
# address, which varies, so it is replaced by "<address>".
actual="${output_dir}/small-struct-return.actual"
awk '/^\.\.[a-z_]*\(\):::EXIT/ { ppt = ($0 ~ /^\.\.main\(/) ? "" : $0; next }
     /^$/ { ppt = ""; next }
     ppt != "" && /^return/ { var = $0; getline value; getline modbit
                              if (value ~ /^0x/) value = "<address>"
                              print ppt, var, value, modbit }' \
    "${dtrace}" > "${actual}"

if ! diff -u "${test_dir}/small-struct-return.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from small-struct-return.goal" >&2
  exit 1
fi

echo "$0: PASSED"
