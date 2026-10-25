#!/bin/bash

# Tests that Fjalar prints nothing but Valgrind's messages when no debugging
# option is given.
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

    # Each of Valgrind's messages starts with the process ID, as in "==1234==".
    if grep -qvE '^==[0-9]+==' "${out}"; then
      echo "$0: FAILED (${src} ${opt}): Fjalar printed output other than Valgrind's messages:" >&2
      grep -vE '^==[0-9]+==' "${out}" >&2
      exit 1
    fi
  done
done

echo "$0: PASSED"
