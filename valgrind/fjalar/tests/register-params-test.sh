#!/bin/bash

# Tests that Fjalar traces formal parameters whose location is a register.
#
# In optimized code, a formal parameter's location may be a register
# (DW_OP_reg*) rather than a stack slot.  Fjalar must output such a parameter's
# value at function entrance and, like a parameter on the stack, the same
# value at function exit.  DynComp must compute its comparability.
#
# Also tests that Fjalar omits a formal parameter whose location it cannot
# read, from both the .decls file and the .dtrace file.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

# Fjalar does not read DWARF 5, and it recognizes a function's entry point
# only at the address in the debugging information, so the executable must not
# be position-independent.  -gno-variable-location-views keeps location view
# pairs out of the .debug_loc section.
gcc -gdwarf-4 -gno-variable-location-views -no-pie -O1 -c \
    -o "${output_dir}/register-params.o" "${test_dir}/register-params.c"
# stack-params.c is a separate compilation unit, because an unoptimized
# function in register-params.c changes the comparability of scale's
# parameters.
gcc -gdwarf-4 -gno-variable-location-views -no-pie -O0 -S -dA \
    -o "${output_dir}/stack-params.s" "${test_dir}/stack-params.c"

# gcc does not emit DW_OP_stack_value after DW_OP_fbreg for a formal parameter
# of an out-of-line function, so rewrite the location of stack_value's v from
# "DW_OP_fbreg N", where N needs 2 bytes, to "DW_OP_fbreg -8;
# DW_OP_stack_value".  The size of the debugging information is unchanged, so
# the offsets that refer to it remain correct.
awk '/DW_AT_name/ && /"v\\0"/ && !done { state = 1 }
     state == 1 && /# DW_OP_fbreg/ { state = 2; print; next }
     state == 2 {
       if ($1 != ".sleb128" || $2 >= -64 || $2 < -8192) {
         print "unexpected location for v: " $0 > "/dev/stderr"; exit 1
       }
       print "\t.sleb128 -8"
       print "\t.byte\t0x9f\t# DW_OP_stack_value"
       state = 0; done = 1; next
     }
     { print }
     END { if (!done) { print "did not find v" > "/dev/stderr"; exit 1 } }' \
    "${output_dir}/stack-params.s" > "${output_dir}/stack-params-v.s"

# Renames formal parameter $1, which has 3 characters, to $2, which has 1
# character, and appends "DW_OP_piece $3" to its location, which is
# "DW_OP_fbreg N" where N needs 1 byte.  The size of the debugging information
# is unchanged.
append_piece() {
  awk -v name="$1" -v newname="$2" -v size="$3" '
     /DW_AT_name/ && index($0, "\"" name "\\0\"") && !done {
       sub(name, newname); state = 1; print; next }
     state == 1 && /# DW_AT_location/ {
       if ($2 != "0x2") {
         print "unexpected location for " name ": " $0 > "/dev/stderr"; exit 1
       }
       print "\t.uleb128 0x4\t# DW_AT_location"; state = 2; next
     }
     state == 2 && /# DW_OP_fbreg/ { state = 3; print; next }
     state == 3 {
       print
       print "\t.byte\t0x93\t# DW_OP_piece"
       print "\t.uleb128 " size
       state = 0; done = 1; next
     }
     { print }
     END { if (!done) { print "did not find " name > "/dev/stderr"; exit 1 } }'
}
append_piece w__ w 8 < "${output_dir}/stack-params-v.s" \
    | append_piece p__ p 4 > "${output_dir}/stack-params-patched.s"
gcc -gdwarf-4 -no-pie -o "${output_dir}/register-params" \
    "${output_dir}/register-params.o" "${output_dir}/stack-params-patched.s"

# register-params.goal assumes that the location of every formal parameter of
# an optimized function is a register throughout its function.  Another compiler version might instead
# use a location list, DW_OP_entry_value, or a constant, or might omit the
# location, for which Fjalar omits the formal parameter.  A line that starts
# with "<depth><offset>:" begins a new debugging information entry.
if readelf --debug-dump=info "${output_dir}/register-params" \
    | awk 'function end_param() { if (inparam && !hasloc) bad = 1; inparam = 0 }
           /^ *<[0-9]+><[0-9a-f]+>:/ { end_param() }
           /DW_TAG_subprogram/ { insub = 1; next }
           insub && /DW_AT_name/ { fname = $NF; insub = 0 }
           # These functions are in stack-params.c, which is not optimized.
           fname ~ /^(stack_value|kept|whole_piece|part_piece)$/ { next }
           /DW_TAG_formal_parameter/ { inparam = 1; hasloc = 0; next }
           inparam && /DW_AT_location/ { hasloc = 1 }
           inparam && /DW_AT_location/ && !/: [0-9]+ byte block: .*\(DW_OP_reg/ { bad = 1 }
           inparam && /DW_AT_const_value/ { bad = 1 }
           END { end_param(); exit !bad }'; then
  readelf --debug-dump=info "${output_dir}/register-params" \
    | grep -A8 DW_TAG_formal_parameter >&2
  # In continuous integration (GitHub Actions sets CI, and Azure Pipelines
  # sets TF_BUILD), fail rather than skip, so that a compiler change that
  # makes this test vacuous does not go unnoticed.
  if [ -n "${CI:-}" ] || [ -n "${TF_BUILD:-}" ]; then
    echo "$0: FAILED: gcc did not put every formal parameter in a register" >&2
    exit 1
  fi
  echo "$0: SKIPPED: gcc did not put every formal parameter in a register" >&2
  exit 0
fi

decls="${output_dir}/register-params.decls"
dtrace="${output_dir}/register-params.dtrace"
status=0
"${valgrind}" --tool=fjalar --dyncomp \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/register-params" \
              > "${output_dir}/register-params.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/register-params.out" >&2
  exit 1
fi

# One line per non-global variable at the first occurrence of each program
# point other than main's (that is, in the first call to each function):
# "<ppt> <variable> <value>", followed by one line per non-global variable
# declared at each program point other than main's:  "<ppt> <variable>
# comparability <comparability>".  The latter shows that Fjalar omits a formal
# parameter whose location it cannot read from the .decls file too.  The order
# of program points in the .decls file depends on function addresses, so the
# latter lines are stably sorted by program point.
actual="${output_dir}/register-params.actual"
awk '/^\.\.[a-z_]*\(\):::/ { ppt = $0; getline; getline
                            if (ppt ~ /^\.\.main\(/ || seen[ppt]++) ppt = ""
                            next }
     ppt == "" { next }
     /^$/ { ppt = ""; next }
     { var = $0; getline; value = $0; getline
       if (var !~ /^::/) print ppt, var, value }' \
    "${dtrace}" > "${actual}"
awk '/^ppt / { ppt = $2 }
     /^  variable / { var = $2 }
     var ~ /^::/ { next }
     /^    comparability / { if (ppt !~ /^\.\.main\(/)
                               print ppt, var, "comparability", $2 }' \
    "${decls}" | LC_ALL=C sort -s -k1,1 >> "${actual}"

if ! diff -u "${test_dir}/register-params.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from register-params.goal" >&2
  exit 1
fi

echo "$0: PASSED"
