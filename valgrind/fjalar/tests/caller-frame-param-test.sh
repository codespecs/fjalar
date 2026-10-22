#!/bin/bash

# Tests that, at function exit, Fjalar visits the value at function entrance
# of a formal parameter that lies in the caller's frame.
#
# A C++ object passed by invisible reference lies in the caller's frame, and
# its location is "DW_OP_fbreg N; DW_OP_deref".  At function entrance, Fjalar
# copies the stack to its virtual stack, so that at function exit it visits
# the same formal parameter values as at function entrance, even if the
# function body changed them.  The copy must include such an object, though
# the object may be far beyond the callee's frame.

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
    -o "${output_dir}/caller-frame-param" "${test_dir}/caller-frame-param.cc"

# mutate's a and b must have the location "DW_OP_fbreg N; DW_OP_deref".
if ! readelf --debug-dump=info "${output_dir}/caller-frame-param" \
    | awk '/DW_TAG_subprogram/ { insub = 1; next }
           insub && /DW_AT_name/ { fname = $NF; insub = 0 }
           fname == "mutate" && /DW_TAG_formal_parameter/ { inparam = 1; next }
           inparam && /DW_AT_location/ {
             inparam = 0
             if (/\(DW_OP_fbreg: -?[0-9]+; DW_OP_deref\)/) found++
           }
           END { exit found != 2 }'; then
  unsuitable_compiler "the locations of mutate's a and b are not \"DW_OP_fbreg N; DW_OP_deref\""
fi

decls="${output_dir}/caller-frame-param.decls"
dtrace="${output_dir}/caller-frame-param.dtrace"
status=0
"${valgrind}" --tool=fjalar --dyncomp \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/caller-frame-param" \
              > "${output_dir}/caller-frame-param.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/caller-frame-param.out" >&2
  exit 1
fi

# One line per occurrence of a.count or b.count at mutate's program points:
# "<ppt> <variable> <value>".  In a program point name, "\_" encodes a space.
actual="${output_dir}/caller-frame-param.actual"
awk '/^\.\.mutate\(Counted,\\_Counted\):::/ { ppt = $0; next }
     /^$/ { ppt = ""; next }
     ppt != "" && ($0 == "a.count" || $0 == "b.count") {
       var = $0; getline; print ppt, var, $0
     }' \
    "${dtrace}" > "${actual}"

if ! diff -u "${test_dir}/caller-frame-param.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from caller-frame-param.goal" >&2
  exit 1
fi

echo "$0: PASSED"
