#!/bin/bash

# Tests that, under --dyncomp-interactions=comparisons, a 64-bit or 128-bit
# load does not make the fields it reads comparable, and that a 64-bit or
# 128-bit copy gives each copied field the comparability of its source field.
# In that mode, only comparisons are interactions.  The expected
# comparability is in dyncomp-copy.goal.

exec "$(dirname "$0")/dyncomp-comparability-driver.sh" dyncomp-copy '' \
     --dyncomp-interactions=comparisons
