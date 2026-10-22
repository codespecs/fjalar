#!/bin/bash

# Tests that Fjalar computes the address of a formal parameter whose location
# is "DW_OP_fbreg N; DW_OP_deref" from the stack slot's value at function
# entrance.
#
# A C++ object passed by invisible reference has such a location.  At function
# exit, the function body may have overwritten the stack slot at DW_OP_fbreg N,
# so Fjalar must dereference the copy of the slot in its virtual stack, not the
# slot itself.  Otherwise, Fjalar reads the parameter from the wrong object.

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
# be position-independent.
g++ -gdwarf-4 -gno-variable-location-views -no-pie -O0 \
    -o "${output_dir}/deref-param" "${test_dir}/deref-param.cc"

# observe's c must have the location "DW_OP_fbreg N; DW_OP_deref".
if ! readelf --debug-dump=info "${output_dir}/deref-param" \
    | awk '/DW_TAG_subprogram/ { insub = 1; next }
           insub && /DW_AT_name/ { fname = $NF; insub = 0 }
           fname == "observe" && /DW_TAG_formal_parameter/ { inparam = 1; next }
           inparam && /DW_AT_location/ { found = /\(DW_OP_fbreg: -?[0-9]+; DW_OP_deref\)/; exit }
           END { exit !found }'; then
  unsuitable_compiler "the location of observe's c is not \"DW_OP_fbreg N; DW_OP_deref\""
fi

# Running the program without Fjalar checks that observe overwrites the stack
# slot, so that this test is not vacuous.
status=0
"${output_dir}/deref-param" || status=$?
if [ "${status}" -ne 0 ]; then
  unsuitable_compiler "observe did not find the stack slot that holds the address of c"
fi

decls="${output_dir}/deref-param.decls"
dtrace="${output_dir}/deref-param.dtrace"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/deref-param" \
              > "${output_dir}/deref-param.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/deref-param.out" >&2
  exit 1
fi

# One line per occurrence of c.count at observe's program points:
# "<ppt> c.count <value>".
actual="${output_dir}/deref-param.actual"
awk '/^\.\.observe\(Counted\):::/ { ppt = $0; next }
     /^$/ { ppt = ""; next }
     ppt != "" && $0 == "c.count" { getline; print ppt, "c.count", $0 }' \
    "${dtrace}" > "${actual}"

if ! diff -u "${test_dir}/deref-param.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from deref-param.goal" >&2
  exit 1
fi

echo "$0: PASSED"
