#!/bin/bash

# Tests DynComp's comparability:  whether the variables at each exit
# program point are comparable to each other.  The expected comparability is
# in dyncomp-comparability.goal, under both --dyncomp-interactions=all and
# --dyncomp-interactions=units.

for interactions in all units; do
  "$(dirname "$0")/dyncomp-comparability-driver.sh" dyncomp-comparability '' \
      --dyncomp-interactions="${interactions}" \
    || { echo "$0: FAILED under --dyncomp-interactions=${interactions}" >&2
         exit 1; }
done
