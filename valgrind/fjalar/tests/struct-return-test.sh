#!/bin/bash

# Tests that Fjalar reads a struct, union, or class return value of at most
# 16 bytes from where the amd64 ABI puts it.
#
# The System V amd64 ABI returns such a value in %rax, %rdx, %xmm0, %xmm1, or
# %st(0), depending on the types of its fields, or in memory if it has an
# unaligned field.  The Itanium C++ ABI returns a class that is non-trivial
# for the purposes of calls in memory.  For a value that is returned in
# memory, %rax holds its address.

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
gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/struct-return" \
    "${test_dir}/struct-return.c"
# C++17 guarantees copy elision, so a function can return a class whose copy
# constructor is deleted.
g++ -std=c++17 -gdwarf-4 -no-pie -O0 -o "${output_dir}/struct-return-cxx" \
    "${test_dir}/struct-return-cxx.cc"

for program in struct-return struct-return-cxx; do
  dtrace="${output_dir}/${program}.dtrace"
  status=0
  "${valgrind}" --tool=fjalar \
                --decls-file="${output_dir}/${program}.decls" \
                --dtrace-file="${dtrace}" \
                "${output_dir}/${program}" \
                > "${output_dir}/${program}.out" 2>&1 || status=$?

  if [ "${status}" -ne 0 ]; then
    echo "$0: FAILED: Fjalar exited with status ${status} on ${program}" >&2
    cat "${output_dir}/${program}.out" >&2
    exit 1
  fi

  # One line per field of the return value of a function other than main:
  # "<ppt> <variable> <value>".  A struct-valued field's value is an address,
  # which varies, so omit it.
  actual="${output_dir}/${program}.actual"
  awk '/^\.\.[A-Za-z0-9_]*\(\):::EXIT/ { ppt = ($0 ~ /^\.\.main\(/) ? "" : $0; next }
       /^$/ { ppt = ""; next }
       ppt != "" && /^return\./ { var = $0; getline value; getline modbit
                                  if (value !~ /^0x/) print ppt, var, value }' \
      "${dtrace}" > "${actual}"

  if ! diff -u "${test_dir}/${program}.goal" "${actual}" >&2; then
    echo "$0: FAILED: output differs from ${program}.goal" >&2
    exit 1
  fi
done

echo "$0: PASSED"
