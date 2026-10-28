#!/bin/bash

# Tests that a 256-bit store writes the tag of the stored value to all 32
# bytes that it writes.  The expected comparability is in
# dyncomp-wide-store.goal.
#
# The test also checks that the IR of the test program stores a V256
# temporary, so that it is not vacuous.

set -e

# Fails in continuous integration (GitHub Actions sets CI, and Azure Pipelines
# sets TF_BUILD), and otherwise skips this test, because this CPU cannot run
# it.  Failing in continuous integration ensures that a change of machines
# that makes this test vacuous does not go unnoticed.  $1 is the reason.
unsuitable_cpu() {
  if [ -n "${CI:-}" ] || [ -n "${TF_BUILD:-}" ]; then
    echo "$0: FAILED: $1" >&2
    exit 1
  fi
  echo "$0: SKIPPED: $1" >&2
  exit 0
}

if ! grep -qw avx /proc/cpuinfo; then
  unsuitable_cpu "the CPU does not support avx"
fi

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" dyncomp-wide-store \
     '/^==== SB / { inProg = (index($0, "/dyncomp-wide-store+") > 0)
                    delete v256 }
      inProg { for (i = 1; i <= NF; i++)
                 if ($i ~ /^t[0-9]+:V256$/) { split($i, p, ":"); v256[p[1]] = 1 } }
      inProg && /STle\(.*\) = t[0-9]+$/ && ($NF in v256) { found = 1 }
      END { exit !found }'
