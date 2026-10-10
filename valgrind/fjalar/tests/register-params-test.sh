#!/bin/bash

# Tests that Fjalar traces formal parameters whose location is a register.
#
# In optimized code, a formal parameter's location may be a register
# (DW_OP_reg*) rather than a stack slot.  Fjalar must output such a parameter's
# value at function entrance and, like a parameter on the stack, the same
# value at function exit.  DynComp must compute its comparability.

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
# pairs out of the .debug_loc section, because some versions of Fjalar
# misread them.
gcc -gdwarf-4 -gno-variable-location-views -no-pie -O1 \
    -o "${output_dir}/register-params" "${test_dir}/register-params.c"

decls="${output_dir}/register-params.decls"
dtrace="${output_dir}/register-params.dtrace"
status=0
"${valgrind}" --tool=fjalar --dyncomp \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/register-params" \
              > "${output_dir}/register-params.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/register-params.out" >&2
  exit 1
fi

# One line per variable at each program point of the invocations with nonces 1
# and 2 (the first calls to add and scale):  "<ppt> <variable> <value>",
# followed by one line per variable at each exit program point other than
# main's:  "<ppt> <variable> comparability <comparability>".
actual="${output_dir}/register-params.actual"
awk '/^\.\.[a-z]*\(\):::/ { ppt = $0; getline; getline; nonce = $0; next }
     ppt == "" { next }
     /^$/ { ppt = ""; next }
     { var = $0; getline; value = $0; getline
       if (nonce == 1 || nonce == 2) print ppt, var, value }' \
    "${dtrace}" > "${actual}"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     /^    comparability / { if (ppt ~ /:::EXIT/ && ppt !~ /^\.\.main\(/)
                               print ppt, var, "comparability", $2 }' \
    "${decls}" >> "${actual}"

if ! diff -u "${test_dir}/register-params.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from register-params.goal" >&2
  exit 1
fi

echo "$0: PASSED"
