#!/bin/bash

# Tests that Fjalar traces variables, formal parameters, and return values of
# the 2-byte floating-point types _Float16 (IEEE 754 binary16) and __bf16
# (bfloat16).  The two types have the same size and DWARF encoding, so Fjalar
# distinguishes them by name.  Kvasir must print each value as a double
# (including infinity, NaN, and a subnormal value) and give each variable the
# rep-type double.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

# Fails in continuous integration (GitHub Actions sets CI, and Azure Pipelines
# sets TF_BUILD), and otherwise skips this test, because this compiler cannot
# run it.  Failing in continuous integration ensures that a compiler change
# that makes this test vacuous does not go unnoticed.  $1 is the reason.
unsuitable_compiler() {
  if [ -n "${CI:-}" ] || [ -n "${TF_BUILD:-}" ]; then
    echo "$0: FAILED: $1" >&2
    exit 1
  fi
  echo "$0: SKIPPED: $1" >&2
  exit 0
}

# Fjalar does not read DWARF 5, and it recognizes a function's entry point
# only at the address in the debugging information, so the executable must not
# be position-independent.  GCC supports arithmetic on __bf16 since version 13.
if ! gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/float16" \
       "${test_dir}/float16.c" 2> "${output_dir}/gcc.out"; then
  cat "${output_dir}/gcc.out" >&2
  unsuitable_compiler "gcc cannot compile _Float16 and __bf16 arithmetic"
fi

decls="${output_dir}/float16.decls"
dtrace="${output_dir}/float16.dtrace"
status=0
"${valgrind}" --tool=fjalar --dyncomp \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/float16" \
              > "${output_dir}/float16.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/float16.out" >&2
  exit 1
fi

# One line per variable at the first occurrence of each program point:
# "<ppt> <variable> <value>", followed by one line per variable declared at
# each program point:  "<ppt> <variable> <dec-type> <rep-type>".  Global
# variables appear only at main's program points, and a hashcode (an address,
# which depends on the linker) does not appear.  The order of program points
# in the .decls file depends on function addresses, so the latter lines are
# stably sorted by program point.
actual="${output_dir}/float16.actual"
awk '/^\.\.[a-z_0-9]*\(\):::/ { ppt = $0; getline; getline
                               if (seen[ppt]++) ppt = ""
                               next }
     ppt == "" { next }
     /^$/ { ppt = ""; next }
     { var = $0; getline; value = $0; getline
       if ((var ~ /^::/ && ppt !~ /^\.\.main\(/) || value ~ /^0x/) next
       print ppt, var, value }' \
    "${dtrace}" > "${actual}"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     /^    rep-type / { reptype = $2 }
     /^    dec-type / { if (var !~ /^::/ || ppt ~ /^\.\.main\(/)
                        print ppt, var, $2, reptype }' \
    "${decls}" | LC_ALL=C sort -s -k1,1 >> "${actual}"

if ! diff -u "${test_dir}/float16.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from float16.goal" >&2
  exit 1
fi

echo "$0: PASSED"
