#!/bin/bash

# Tests that a 128-bit or 256-bit store writes the tag of the stored value to
# every byte that it writes, that, under --dyncomp-interactions=all, a 128-bit
# or 256-bit load merges nothing, and that a 256-bit load and store in one
# superblock give each copied byte the tag of its source byte.  The expected
# comparability is in dyncomp-wide-move.goal.  The dyncomp-wide-move-*-test.sh
# scripts test the other values of --dyncomp-interactions.
#
# The test also checks that one copy_256_* superblock stores the V256
# temporary that it loaded, so that it is not vacuous.

set -e

. "$(dirname "$0")/environment-checks.sh"

require_cpu_flags "$0" avx

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" dyncomp-wide-move \
     '/^==== SB / { if (inCopy && store && load) { found = 1 }
                    inCopy = ($0 ~ / copy_256_[0-9]+(\+[^ ]*)? /)
                    store = load = 0
                    delete loaded }
      inCopy && /^[[:space:]]*t[0-9]+ = LDle:V256\(/ {
        loaded[$1] = 1
        load = 1
      }
      inCopy && /STle\(.*\) = t[0-9]+$/ && ($NF in loaded) { store = 1 }
      END { exit !(found || (inCopy && store && load)) }'
