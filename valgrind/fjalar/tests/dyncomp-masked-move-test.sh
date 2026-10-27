#!/bin/bash

# Tests that DynComp instruments guarded loads and guarded stores, which VEX
# translates each lane of vmaskmovps to:  a lane that is loaded or stored
# should carry its tag, and a lane that is not should carry none.  The
# expected comparability is in dyncomp-masked-move.goal.
#
# The test also checks that the IR of the test program contains a guarded
# load and a guarded store, so that it is not vacuous.

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

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" dyncomp-masked-move \
     '/^==== SB / { inProg = (index($0, "/dyncomp-masked-move+") > 0) }
      inProg && / = if-strict \(t[0-9]+\) Ident32\(LDle\(/ { load = 1 }
      inProg && /if \(t[0-9]+\) \{ STle\(/ { store = 1 }
      END { exit !(load && store) }'
