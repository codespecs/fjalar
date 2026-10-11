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
# pairs out of the .debug_loc section.
gcc -gdwarf-4 -gno-variable-location-views -no-pie -O1 \
    -o "${output_dir}/register-params" "${test_dir}/register-params.c"

# register-params.goal assumes that the location of every formal parameter is
# a register throughout its function.  Another compiler version might instead
# use a location list, DW_OP_entry_value, or a constant, for which Fjalar omits
# the formal parameter.
if readelf --debug-dump=info "${output_dir}/register-params" \
    | awk '/DW_TAG_formal_parameter/ { inparam = 1; next }
           /DW_TAG_/ { inparam = 0 }
           inparam && /DW_AT_location/ && !/: [0-9]+ byte block: .*\(DW_OP_reg/ { bad = 1 }
           inparam && /DW_AT_const_value/ { bad = 1 }
           END { exit !bad }'; then
  readelf --debug-dump=info "${output_dir}/register-params" \
    | grep -A8 DW_TAG_formal_parameter >&2
  # In continuous integration (GitHub Actions sets CI, and Azure Pipelines
  # sets TF_BUILD), fail rather than skip, so that a compiler change that
  # makes this test vacuous does not go unnoticed.
  if [ -n "${CI:-}" ] || [ -n "${TF_BUILD:-}" ]; then
    echo "$0: FAILED: gcc did not put every formal parameter in a register" >&2
    exit 1
  fi
  echo "$0: SKIPPED: gcc did not put every formal parameter in a register" >&2
  exit 0
fi

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

# One line per non-global variable at the first occurrence of each program
# point other than main's (that is, in the first call to each function):
# "<ppt> <variable> <value>", followed by one line per non-global variable at
# each exit program point other than main's:  "<ppt> <variable> comparability
# <comparability>".
actual="${output_dir}/register-params.actual"
awk '/^\.\.[a-z]*\(\):::/ { ppt = $0; getline; getline
                            if (ppt ~ /^\.\.main\(/ || seen[ppt]++) ppt = ""
                            next }
     ppt == "" { next }
     /^$/ { ppt = ""; next }
     { var = $0; getline; value = $0; getline
       if (var !~ /^::/) print ppt, var, value }' \
    "${dtrace}" > "${actual}"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     var ~ /^::/ { next }
     /^    comparability / { if (ppt ~ /:::EXIT/ && ppt !~ /^\.\.main\(/)
                               print ppt, var, "comparability", $2 }' \
    "${decls}" >> "${actual}"

if ! diff -u "${test_dir}/register-params.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from register-params.goal" >&2
  exit 1
fi

echo "$0: PASSED"
