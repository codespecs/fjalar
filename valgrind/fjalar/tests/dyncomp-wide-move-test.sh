#!/bin/bash

# Tests that a 128-bit or 256-bit store writes the tag of the stored value to
# every byte that it writes, that, under --dyncomp-interactions=all, a 128-bit
# or 256-bit load merges nothing, and that a 256-bit load and store in one
# superblock give each copied byte the tag of its source byte.  The expected
# comparability is in dyncomp-wide-move.goal.  The dyncomp-wide-move-*-test.sh
# scripts test the other values of --dyncomp-interactions.
#
# The test also checks that the IR of the test program stores a V256
# temporary and contains a 256-bit load, so that it is not vacuous.

set -e

. "$(dirname "$0")/environment-checks.sh"

require_cpu_flags "$0" avx

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" dyncomp-wide-move \
     '/^==== SB / { inProg = (index($0, "/dyncomp-wide-move+") > 0)
                    delete v256 }
      inProg { for (i = 1; i <= NF; i++)
                 if ($i ~ /^t[0-9]+:V256$/) { split($i, p, ":"); v256[p[1]] = 1 } }
      inProg && /STle\(.*\) = t[0-9]+$/ && ($NF in v256) { store = 1 }
      inProg && /LDle:V256\(/ { load = 1 }
      END { exit !(store && load) }'
