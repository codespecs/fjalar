#!/bin/bash

# Tests that Fjalar reports an error, rather than crashing, on a program whose
# debugging information is all DWARF 5, which Fjalar does not read.
#
# Fjalar skips each compilation unit whose DWARF version it does not read.  If
# it skips them all, it finds no debugging information entries, and it must
# not allocate an array of zero entries, because VG_(calloc) of zero elements
# fails an assertion.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

gcc -gdwarf-5 -no-pie -o "${output_dir}/dwarf5-unsupported" \
    "${test_dir}/dwarf5-unsupported.c"

out="${output_dir}/dwarf5-unsupported.out"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${output_dir}/dwarf5-unsupported.decls" \
              --dtrace-file="${output_dir}/dwarf5-unsupported.dtrace" \
              "${output_dir}/dwarf5-unsupported" \
              > "${out}" 2>&1 || status=$?

if [ "${status}" -ne 1 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}, not 1" >&2
  cat "${out}" >&2
  exit 1
fi

if ! grep -q 'Error - No functions were found' "${out}"; then
  echo "$0: FAILED: Fjalar did not report that it found no functions" >&2
  cat "${out}" >&2
  exit 1
fi

echo "$0: PASSED"
