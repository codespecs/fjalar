#!/bin/bash

# Tests that DynComp instruments guarded loads and guarded stores, which VEX
# translates each lane of vmaskmovps and vmaskmovpd to, and each XMM register
# that xsave saves or xrstor restores.  A lane that is loaded or stored should
# carry the tag of the value that is moved.  The expected comparability is in
# dyncomp-masked-move.goal.  The dyncomp-masked-move-*-test.sh scripts test
# the other values of --dyncomp-interactions.
#
# The test also checks that the IR of the test program contains a guarded
# load of each size (32-bit, 64-bit, and 128-bit) and a guarded store, so that
# it is not vacuous.

set -e

. "$(dirname "$0")/environment-checks.sh"

require_cpu_flags "$0" avx xsave

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" dyncomp-masked-move \
     '/^==== SB / { inProg = (index($0, "/dyncomp-masked-move+") > 0) }
      inProg && / = if-strict \(t[0-9]+\) Ident32\(LDle\(/ { load32 = 1 }
      inProg && / = if-strict \(t[0-9]+\) Ident64\(LDle\(/ { load64 = 1 }
      inProg && / = if-strict \(t[0-9]+\) IdentV128\(LDle\(/ { load128 = 1 }
      inProg && /if \(t[0-9]+\) \{ STle\(/ { store = 1 }
      END { exit !(load32 && load64 && load128 && store) }'
