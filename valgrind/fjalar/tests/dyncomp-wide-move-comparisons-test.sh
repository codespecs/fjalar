#!/bin/bash

# Tests that, under --dyncomp-interactions=comparisons, a 128-bit or 256-bit store
# writes the tag of the stored value to every byte that it writes, and that a
# 128-bit or 256-bit load merges nothing.  dyncomp-wide-move-test.sh describes
# the test.  The expected comparability is in dyncomp-wide-move-comparisons.goal.

set -e

. "$(dirname "$0")/environment-checks.sh"

require_cpu_flags "$0" avx

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" \
     --program=dyncomp-wide-move dyncomp-wide-move-comparisons '' \
     --dyncomp-interactions=comparisons
