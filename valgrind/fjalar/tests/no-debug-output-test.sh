#!/bin/bash

# Tests that Fjalar prints nothing but Valgrind's messages and warnings about
# the debugging information when no debugging option is given.
#
# Fjalar's copy of Binutils' dwarf.c prints a dump of the debugging
# information only with --fjalar-debug-dump, so each of its output statements
# must be guarded.  An unguarded one prints to the user of every program whose
# debugging information reaches it.  For example, the location lists of
# optimized code reach the code that prints " (start == end)".

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

. "${test_dir}/environment-checks.sh"

# The suffixes that display_loc_list prints after some location list entries.
loc_list_suffixes='\[without DW_AT_frame_base\]|\(start == end\)|\(start > end\)'
# Whether the dump of some program's debugging information contains one of
# loc_list_suffixes.
reached_loc_list_suffixes=false

# Each of Valgrind's messages starts with the process ID, as in "==1234==".
# Warnings and errors about the debugging information, such as that of the C
# runtime, are not part of the dump of the debugging information.
expected_output='^(==[0-9]+==|dwarf\.c: (Warning|Error): )'

for src in deref-param.cc location-views.c; do
  case "${src}" in
    *.c) compiler=gcc ;;
    *) compiler=g++ ;;
  esac
  for opt in -O0 -O2; do
    program="${output_dir}/${src%.*}${opt}"
    # Fjalar does not read DWARF 5, and it recognizes a function's entry point
    # only at the address in the debugging information, so the executable must
    # not be position-independent.
    "${compiler}" -gdwarf-4 -no-pie "${opt}" -o "${program}" "${test_dir}/${src}"

    if "${valgrind}" --tool=fjalar --no-dyncomp --decls-only --fjalar-debug-dump \
                     --decls-file="${program}.decls" "${program}" 2>&1 \
         | grep -qE "${loc_list_suffixes}"; then
      reached_loc_list_suffixes=true
    fi

    out="${program}.out"
    status=0
    # With DynComp, which is the default, Fjalar ignores --decls-only.
    "${valgrind}" --tool=fjalar --no-dyncomp --decls-only \
                  --decls-file="${program}.decls" \
                  "${program}" > "${out}" 2>&1 || status=$?
    if [ "${status}" -ne 0 ]; then
      echo "$0: FAILED (${src} ${opt}): Fjalar exited with status ${status}" >&2
      cat "${out}" >&2
      exit 1
    fi

    if grep -qvE "${expected_output}" "${out}"; then
      echo "$0: FAILED (${src} ${opt}): Fjalar printed output other than Valgrind's messages:" >&2
      grep -vE "${expected_output}" "${out}" >&2
      exit 1
    fi
  done
done

if [ "${reached_loc_list_suffixes}" = false ]; then
  unsuitable_environment "$0" "no location list entry gets a suffix such as \" (start == end)\""
fi

echo "$0: PASSED"
