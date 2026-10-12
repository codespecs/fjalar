#!/bin/bash

# Tests that Fjalar omits a formal parameter whose location it cannot read,
# from both the .decls file and the .dtrace file.

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
gcc -gdwarf-4 -gno-variable-location-views -no-pie -O1 -S -dA \
    -o "${output_dir}/omitted-params.s" "${test_dir}/omitted-params.c"

# gcc does not emit DW_OP_stack_value after DW_OP_fbreg for a formal parameter
# of an out-of-line function, so rewrite the location of stack_value's x from
# "DW_OP_fbreg N", where N needs 2 bytes, to "DW_OP_fbreg -8;
# DW_OP_stack_value".  The size of the debugging information is unchanged, so
# the offsets that refer to it remain correct.
awk '/DW_AT_name/ && /"x\\0"/ && !done { state = 1 }
     state == 1 && /# DW_OP_fbreg/ { state = 2; print; next }
     state == 2 {
       if ($1 != ".sleb128" || $2 >= -64 || $2 < -8192) {
         print "unexpected location for x: " $0 > "/dev/stderr"; exit 1
       }
       print "\t.sleb128 -8"
       print "\t.byte\t0x9f\t# DW_OP_stack_value"
       state = 0; done = 1; next
     }
     { print }
     END { if (!done) { print "did not find x" > "/dev/stderr"; exit 1 } }' \
    "${output_dir}/omitted-params.s" > "${output_dir}/omitted-params-x.s"

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
append_piece w__ w 8 < "${output_dir}/omitted-params-x.s" \
    | append_piece p__ p 4 > "${output_dir}/omitted-params-patched.s"
gcc -gdwarf-4 -no-pie \
    -o "${output_dir}/omitted-params" "${output_dir}/omitted-params-patched.s"

decls="${output_dir}/omitted-params.decls"
dtrace="${output_dir}/omitted-params.dtrace"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/omitted-params" \
              > "${output_dir}/omitted-params.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/omitted-params.out" >&2
  exit 1
fi

# One line per non-global variable declared at each program point other than
# main's:  "decls <ppt> <variable>", and one line per non-global variable at
# the first occurrence of each program point other than main's:
# "dtrace <ppt> <variable>".  The lines are sorted, because the order of
# program points in the .decls file depends on Fjalar's hash table.
actual="${output_dir}/omitted-params.actual"
{
awk '/^ppt / { ppt = $2 }
     /^  variable / { if ($2 !~ /^::/ && ppt !~ /^\.\.main\(/)
                        print "decls", ppt, $2 }' \
    "${decls}"
awk '/^\.\.[A-Za-z0-9_]*\(\):::/ { ppt = $0; getline; getline
                                     if (ppt ~ /^\.\.main\(/ || seen[ppt]++) ppt = ""
                                     next }
     ppt == "" { next }
     /^$/ { ppt = ""; next }
     { var = $0; getline; getline
       if (var !~ /^::/) print "dtrace", ppt, var }' \
    "${dtrace}"
} | LC_ALL=C sort > "${actual}"

if ! diff -u "${test_dir}/omitted-params.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from omitted-params.goal" >&2
  exit 1
fi

echo "$0: PASSED"
