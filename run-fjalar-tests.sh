#!/bin/bash

# Run the Fjalar tests that do not depend on Daikon:  every *-test.sh script
# in valgrind/fjalar/tests/.  Run every test, even after one fails, then list
# the tests that failed.
#
# Usage: ./run-fjalar-tests.sh

FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"
cd "$FJALARDIR" || exit 2

failed=()
for t in valgrind/fjalar/tests/*-test.sh; do
  echo "Running $t"
  "$t" || failed+=("$t")
done

if [ ${#failed[@]} -gt 0 ]; then
  echo "Failed tests:" >&2
  printf '  %s\n' "${failed[@]}" >&2
  exit 1
fi
