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

. "${test_dir}/environment-checks.sh"

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
  unsuitable_environment "$0" "the locations of leaf's a and b are not \"DW_OP_breg7 (rsp): N\" with N < 0"
fi

exec "${test_dir}/dyncomp-comparability-driver.sh" dyncomp-red-zone-param ''
