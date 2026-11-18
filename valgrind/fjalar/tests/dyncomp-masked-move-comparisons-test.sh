#!/bin/bash

# Tests that, under --dyncomp-interactions=comparisons, DynComp instruments guarded
# loads and guarded stores.  dyncomp-masked-move-test.sh describes the test.
# The expected comparability is in dyncomp-masked-move-comparisons.goal.

set -e

. "$(dirname "$0")/environment-checks.sh"

require_cpu_flags "$0" avx xsave

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" \
     --program=dyncomp-masked-move dyncomp-masked-move-comparisons '' \
     --dyncomp-interactions=comparisons
