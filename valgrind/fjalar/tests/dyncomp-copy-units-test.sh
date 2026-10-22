#!/bin/bash

# Tests that, under --dyncomp-interactions=units, a 64-bit or 128-bit load does
# not make the fields it reads comparable.  In that mode, a load is not an
# interaction.  The expected comparability is in dyncomp-copy.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" dyncomp-copy '' \
     --dyncomp-interactions=units
