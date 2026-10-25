#!/bin/bash

# Tests that Fjalar reports the compilation units whose DWARF version it does
# not read, such as DWARF 5.
#
# Fjalar skips each compilation unit whose DWARF version it does not read.  If
# it skips them all, it finds no debugging information entries, and it must
# report an error rather than crash.  If it skips only some of them, it must
# warn that it omits their functions.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

# Runs Fjalar on the program compiled from dwarf5-unsupported-main.c, with the
# DWARF version given by $1, and dwarf5-unsupported.c, with DWARF version 5.
# Sets "out" and "decls" to the names of Fjalar's output and .decls files, and
# "status" to Fjalar's exit status.
run_fjalar() {
  local main_version="$1"
  local prog="${output_dir}/main-dwarf${main_version}"
  gcc -gdwarf-"${main_version}" -no-pie -c -o "${prog}-main.o" \
      "${test_dir}/dwarf5-unsupported-main.c"
  gcc -gdwarf-5 -no-pie -c -o "${prog}-add.o" "${test_dir}/dwarf5-unsupported.c"
  gcc -no-pie -o "${prog}" "${prog}-main.o" "${prog}-add.o"

  out="${prog}.out"
  decls="${prog}.decls"
  status=0
  "${valgrind}" --tool=fjalar \
                --decls-file="${decls}" \
                --dtrace-file="${prog}.dtrace" \
                "${prog}" > "${out}" 2>&1 || status=$?
}

# Fails the test if Fjalar's output does not contain the given text.
expect_output() {
  if ! grep -q -- "$1" "${out}"; then
    echo "$0: FAILED: Fjalar's output does not contain \"$1\"" >&2
    cat "${out}" >&2
    exit 1
  fi
}

hint='Did you compile your program'

# All of the debugging information is DWARF 5.
run_fjalar 5
if [ "${status}" -ne 1 ]; then
  echo "$0: FAILED (all DWARF 5): Fjalar exited with status ${status}, not 1" >&2
  cat "${out}" >&2
  exit 1
fi
expect_output 'Error - No functions were found, because Fjalar does not read the DWARF'
expect_output "${hint}"

# Only some of the debugging information is DWARF 5.
run_fjalar 4
if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED (some DWARF 5): Fjalar exited with status ${status}, not 0" >&2
  cat "${out}" >&2
  exit 1
fi
expect_output 'Warning - Fjalar omits the functions of [0-9]* compilation unit(s), because'
expect_output "${hint}"
if ! grep -q '^ppt \.\.main():::ENTER$' "${decls}"; then
  echo "$0: FAILED (some DWARF 5): no program point for main() in ${decls}" >&2
  cat "${out}" >&2
  exit 1
fi

echo "$0: PASSED"
