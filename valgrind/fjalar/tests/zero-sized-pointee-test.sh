#!/bin/bash

# Tests that Fjalar traces a pointer whose target type occupies 0 bytes.
#
# To determine how many elements a pointer refers to, Fjalar divides by the
# number of bytes between elements, which is the size of the target type.
# When that size is 0 -- as it is for Rust's `*const ()` and for a C pointer
# to a zero-sized struct -- the division traps and Fjalar dies of SIGFPE
# before it writes the program point's exit.

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
gcc -gdwarf-4 -no-pie -o "${output_dir}/zero-sized-pointee" \
    "${test_dir}/zero-sized-pointee.c"

dtrace="${output_dir}/zero-sized-pointee.dtrace"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${output_dir}/zero-sized-pointee.decls" \
              --dtrace-file="${dtrace}" \
              "${output_dir}/zero-sized-pointee" \
              > "${output_dir}/zero-sized-pointee.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/zero-sized-pointee.out" >&2
  exit 1
fi

if ! grep -q '^\.\.observe():::EXIT' "${dtrace}"; then
  echo "$0: FAILED: no exit program point for observe() in ${dtrace}" >&2
  cat "${output_dir}/zero-sized-pointee.out" >&2
  exit 1
fi

echo "$0: PASSED"
