#!/bin/bash

# Tests that, at function entrance, Fjalar keeps the tags of a formal
# parameter that lies in the red zone below the stack pointer, at a location
# relative to the stack pointer.  The expected comparability is in
# dyncomp-red-zone-param.goal.
#
# The test also checks that the locations of leaf's formal parameters are
# below the stack pointer, so that it is not vacuous.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"

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

# Compile as dyncomp-comparability-driver.sh does.
gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/dyncomp-red-zone-param" \
    "${test_dir}/dyncomp-red-zone-param.c"

# leaf's a and b must have the location "DW_OP_breg7 (rsp): N" with N < 0.
if ! readelf --debug-dump=info "${output_dir}/dyncomp-red-zone-param" \
    | awk '/DW_TAG_subprogram/ { insub = 1; fname = ""; next }
           /DW_TAG_/ { insub = 0 }
           insub && /DW_AT_name/ { fname = $NF; insub = 0 }
           fname == "leaf" && /DW_TAG_formal_parameter/ { inparam = 1; next }
           inparam && /DW_AT_location/ {
             inparam = 0
             if (/\(DW_OP_breg7 \(rsp\): -[0-9]+\)/) found++
           }
           END { exit found != 2 }'; then
  unsuitable_compiler "the locations of leaf's a and b are not \"DW_OP_breg7 (rsp): N\" with N < 0"
fi

exec "${test_dir}/dyncomp-comparability-driver.sh" dyncomp-red-zone-param ''
