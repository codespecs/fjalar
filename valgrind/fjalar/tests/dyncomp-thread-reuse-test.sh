#!/bin/bash

# Tests that a new thread does not start with the tags of an exited thread
# whose Valgrind thread slot it reuses.  The tag garbage collector does not
# renumber the tags in an empty slot, so those tags are stale.  The program
# dyncomp-thread-reuse.c arranges that the collector runs while the slot is
# empty and while the new thread runs; then the collector finds any stale
# tag in the new thread's guest state, because the tag is at least nextTag,
# and it reports the number of stale tags that it found.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

# Fjalar does not read DWARF 5.
gcc -gdwarf-4 -no-pie -O0 -pthread -o "${output_dir}/dyncomp-thread-reuse" \
    "${test_dir}/dyncomp-thread-reuse.c"

out="${output_dir}/dyncomp-thread-reuse.out"
status=0
"${valgrind}" --tool=fjalar --dyncomp --dyncomp-gc-num-tags=10000 \
              --decls-only --decls-file="${output_dir}/dyncomp-thread-reuse.decls" \
              "${output_dir}/dyncomp-thread-reuse" > "${out}" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  tail -n 100 "${out}" >&2
  exit 1
fi

if ! grep -q "Done garbage collecting" "${out}"; then
  echo "$0: FAILED: the tag garbage collector did not run" >&2
  exit 1
fi

if grep "stale tags" "${out}" >&2; then
  echo "$0: FAILED: the tag garbage collector found stale tags" >&2
  exit 1
fi

echo "$0: PASSED"
