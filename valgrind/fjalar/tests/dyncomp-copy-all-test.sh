#!/bin/bash

# Tests that, under --dyncomp-interactions=all, a 128-bit load does not make
# the fields it reads comparable, and that a 128-bit copy gives each copied
# field the comparability of its source field.  In that mode, a load of at
# most 8 bytes is an interaction, so a 64-bit copy makes the two fields it
# reads comparable.  The expected comparability is in dyncomp-copy-all.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" \
     --program=dyncomp-copy dyncomp-copy-all '' \
     --dyncomp-interactions=all
