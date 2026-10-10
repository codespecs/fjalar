#!/bin/bash

# Tests DynComp's comparability for unary operations whose result is a count
# or a mask computed from the bits of the operand.
#
# Such a result gets tag 0, so it is not comparable to the operand.  The tag
# merges that computed the operand (such as the merge of a and b in
# 'ctz(a + b)') must still take effect, even though the unary operation
# discards the operand's tag.

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
gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/dyncomp-unop-tag0" \
    "${test_dir}/dyncomp-unop-tag0.c"

decls="${output_dir}/dyncomp-unop-tag0.decls"
status=0
"${valgrind}" --tool=fjalar --dyncomp --decls-only --decls-file="${decls}" \
              "${output_dir}/dyncomp-unop-tag0" \
              > "${output_dir}/dyncomp-unop-tag0.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/dyncomp-unop-tag0.out" >&2
  exit 1
fi

# One line per variable at each exit program point, other than main's:
# "<ppt> <variable> <comparability>".
actual="${output_dir}/dyncomp-unop-tag0.comparability"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     /^    comparability / { if (ppt ~ /:::EXIT/ && ppt !~ /^\.\.main\(/)
                               print ppt, var, $2 }' "${decls}" > "${actual}"

if ! diff -u "${test_dir}/dyncomp-unop-tag0.goal" "${actual}" >&2; then
  echo "$0: FAILED: comparability differs from dyncomp-unop-tag0.goal" >&2
  exit 1
fi

echo "$0: PASSED"
