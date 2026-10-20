#!/bin/bash

# Runs a DynComp comparability test; the *-test.sh scripts call it.  Its
# name does not end in "-test.sh", so that it is not run as a test itself.
# Usage: dyncomp-comparability-driver.sh [--program=<program>] <test>
#            <trace-check> <fjalar-option>...
#
# Compiles <program>.c (by default, <test>.c), runs Fjalar with DynComp and
# the given options on it, and compares the comparability of the variables at
# each exit program point (other than main's) with <test>.goal, whose lines
# have the form "<ppt> <variable> <comparability>".  --program lets several
# tests call this script on one program with different options.
#
# <trace-check> is the empty string or an awk program.  The awk program
# reads the trace of the IR of each superblock, after the optimization that
# precedes instrumentation, and exits with status 0 if the IR is as the test
# requires -- for example, if the IR calls a specific helper function.  The
# check is needed because if VEX specialized a helper call into an IR
# operation, then the test would not exercise DynComp's handling of helper
# calls.  If <trace-check> is the empty string, the driver neither traces nor
# checks the IR.

set -e

program=""
case "$1" in
  --program=*) program="${1#--program=}"; shift ;;
esac
if [ $# -lt 2 ]; then
  echo "Usage: $0 [--program=<program>] <test> <trace-check> <fjalar-option>..." >&2
  exit 2
fi
test_name="$1"
trace_check="$2"
shift 2
program="${program:-${test_name}}"

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "${test_name}: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

# Fjalar does not read DWARF 5, and it recognizes a function's entry point
# only at the address in the debugging information, so the executable must not
# be position-independent.
gcc -gdwarf-4 -no-pie -O0 -o "${output_dir}/${program}" \
    "${test_dir}/${program}.c"

# Fjalar disables chasing, so each superblock ends at a jump and VEX cannot
# specialize a helper call that reads the flags set in an earlier basic block.
# The description of <trace-check> above says why that matters.
trace_options=()
if [ -n "${trace_check}" ]; then
  trace_options=(--trace-flags=01000000 --trace-notbelow=0)
fi

decls="${output_dir}/${test_name}.decls"
out="${output_dir}/${test_name}.out"
status=0
"${valgrind}" --tool=fjalar "${trace_options[@]}" --dyncomp "$@" \
              --decls-only --decls-file="${decls}" \
              "${output_dir}/${program}" > "${out}" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "${test_name}: FAILED: Fjalar exited with status ${status}" >&2
  tail -n 100 "${out}" >&2
  exit 1
fi

if [ -n "${trace_check}" ] && ! awk "${trace_check}" "${out}"; then
  echo "${test_name}: FAILED: the IR does not call the expected helpers" >&2
  # Show the IR of the test program's own code, or, if no superblock is in
  # it, the first superblock headers, in case their format has changed.
  awk -v prog="${output_dir}/${program}+" \
      '/^==== SB / { inProg = (index($0, prog) > 0)
                     if (inProg) { found = 1 }
                     else if (++headers <= 10) { others = others $0 "\n" } }
       inProg { print }
       END { if (!found) printf "%s", others }' "${out}" >&2
  exit 1
fi

actual="${output_dir}/${test_name}.comparability"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     /^    comparability / { if (ppt ~ /:::EXIT/ && ppt !~ /^\.\.main\(/)
                               print ppt, var, $2 }' "${decls}" > "${actual}"

if ! diff -u "${test_dir}/${test_name}.goal" "${actual}" >&2; then
  echo "${test_name}: FAILED: comparability differs from ${test_name}.goal" >&2
  exit 1
fi

echo "${test_name}: PASSED"
