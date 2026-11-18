#!/bin/bash

# Runs a test of how Fjalar handles variables of a kind of base type, such
# as a floating-point type; the *-test.sh scripts call it.  Its name does not
# end in "-test.sh", so that it is not run as a test itself.
# Usage: float-types-driver.sh <test>
#
# Compiles <test>.c, runs Kvasir with DynComp on it, and compares the values
# of its variables, and their declared and representation types, with
# <test>.goal.

set -e

if [ $# -ne 1 ]; then
  echo "Usage: $0 <test>" >&2
  exit 2
fi
test_name="$1"

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "${test_name}: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

. "${test_dir}/environment-checks.sh"

# Fjalar does not read DWARF 5, and it recognizes a function's entry point
# only at the address in the debugging information, so the executable must not
# be position-independent.  An older compiler may not support a type that the
# test uses; for example, GCC supports arithmetic on __bf16 since version 13.
if ! gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/${test_name}" \
       "${test_dir}/${test_name}.c" 2> "${output_dir}/gcc.out"; then
  cat "${output_dir}/gcc.out" >&2
  unsuitable_environment "${test_name}" "gcc cannot compile ${test_name}.c"
fi

decls="${output_dir}/${test_name}.decls"
dtrace="${output_dir}/${test_name}.dtrace"
status=0
"${valgrind}" --tool=fjalar --dyncomp \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/${test_name}" \
              > "${output_dir}/${test_name}.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "${test_name}: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/${test_name}.out" >&2
  exit 1
fi

# One line per variable at the first occurrence of each program point:
# "<ppt> <variable> <value>", followed by one line per variable declared at
# each program point:  "<ppt> <variable> <dec-type> <rep-type>".  Global
# variables appear only at main's program points, and a hashcode (an address,
# which depends on the linker) does not appear.  The order of program points
# in the .decls file depends on function addresses, so the latter lines are
# stably sorted by program point.
actual="${output_dir}/${test_name}.actual"
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

if ! diff -u "${test_dir}/${test_name}.goal" "${actual}" >&2; then
  echo "${test_name}: FAILED: output differs from ${test_name}.goal" >&2
  exit 1
fi

echo "${test_name}: PASSED"
