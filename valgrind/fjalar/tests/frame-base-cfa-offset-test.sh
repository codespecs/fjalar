#!/bin/bash

# Tests that Fjalar computes the frame base of a function whose DW_AT_frame_base
# is (DW_OP_call_frame_cfa; DW_OP_consts N; DW_OP_plus), rather than a bare
# DW_OP_call_frame_cfa.
#
# The Rust compiler emits that expression, but GCC emits a bare
# DW_OP_call_frame_cfa, so the test rewrites GCC's debugging information: it
# replaces cfa_offset's frame base with the three-operation form and subtracts
# N from every DW_OP_fbreg offset, which leaves each variable at the same
# address.  So Fjalar reads the formal parameters correctly only if it adds the
# expression's constant to the CFA.  Before Fjalar supported this expression it
# fell back on the frame pointer register, which is 16 bytes below the CFA, and
# read the wrong stack slots.
#
# Rewriting must not change the size of .debug_info, because GCC emits the
# compilation unit's length and its DW_AT_type and DW_AT_sibling offsets as
# literals.  The frame base grows by three bytes, and shortening two inline
# names pays for them; see frame-base-cfa-offset.c.  The shortened names move
# only the formal parameter entries, which nothing refers to.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

for tool in gcc readelf; do
  if ! command -v "${tool}" > /dev/null; then
    echo "$0: missing prerequisite: ${tool}" >&2
    exit 2
  fi
done

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

. "${test_dir}/environment-checks.sh"

# The constant to add to the CFA.  It must be small enough that every shifted
# DW_OP_fbreg offset still fits in a one-byte SLEB128.
offset=16

# Fjalar does not read DWARF 5, and it recognizes a function's entry point only
# at the address in the debugging information, so the executable must not be
# position-independent.  -gno-variable-location-views keeps location view pairs
# out of the .debug_loc section.
gcc -gdwarf-4 -gno-variable-location-views -no-pie -O0 -S -dA \
    -o "${output_dir}/frame-base-cfa-offset.s" "${test_dir}/frame-base-cfa-offset.c"

# Rewrites cfa_offset's frame base and shifts every DW_OP_fbreg offset.  Both
# the old and the new offset must encode as a one-byte SLEB128, or .debug_info
# would change size.
if ! awk -v n="${offset}" '
    /# DW_AT_frame_base$/ {
      if ($1 != ".uleb128" || $2 != "0x1") {
        print "unexpected frame base: " $0 > "/dev/stderr"; exit 1
      }
      getline op
      if (op !~ /# DW_OP_call_frame_cfa$/) {
        print "unexpected frame base operation: " op > "/dev/stderr"; exit 1
      }
      print "\t.uleb128 0x4\t# DW_AT_frame_base"
      print op
      print "\t.byte\t0x11\t# DW_OP_consts"
      print "\t.sleb128 " n
      print "\t.byte\t0x22\t# DW_OP_plus"
      framebase++
      next
    }
    /# DW_AT_name$/ && index($0, "\"abc\\0\"") {
      print "\t.ascii \"a\\0\"\t# DW_AT_name"; abc++; next
    }
    /# DW_AT_name$/ && index($0, "\"de\\0\"") {
      print "\t.ascii \"d\\0\"\t# DW_AT_name"; de++; next
    }
    /# DW_OP_fbreg$/ {
      print
      getline operand
      split(operand, field, " ")
      if (field[1] != ".sleb128") {
        print "unexpected fbreg operand: " operand > "/dev/stderr"; exit 1
      }
      old = field[2] + 0; new = old - n
      if (old < -64 || old > 63 || new < -64 || new > 63) {
        print "fbreg offset " old " -> " new " needs more than one byte" > "/dev/stderr"
        exit 1
      }
      print "\t.sleb128 " new
      fbreg++
      next
    }
    { print }
    END {
      if (framebase != 1 || abc != 1 || de != 1 || fbreg < 2) {
        print "rewrote frame bases: " framebase+0 ", names: " abc+0 " " de+0 \
              ", fbreg offsets: " fbreg+0 > "/dev/stderr"
        exit 1
      }
    }' "${output_dir}/frame-base-cfa-offset.s" \
      > "${output_dir}/frame-base-cfa-offset-patched.s"; then
  unsuitable_environment "$0" "could not rewrite cfa_offset's frame base"
fi

gcc -no-pie -o "${output_dir}/frame-base-cfa-offset" \
    "${output_dir}/frame-base-cfa-offset-patched.s" \
    "${test_dir}/frame-base-cfa-offset-main.c"

# The rewrite must have produced the expression under test, and readelf must
# still be able to read the debugging information around it.
if ! readelf --debug-dump=info "${output_dir}/frame-base-cfa-offset" 2>&1 \
    | awk -v n="${offset}" \
          '/DW_TAG_/ { insub = /DW_TAG_subprogram/; isf = 0; next }
           insub && /DW_AT_name.*: cfa_offset$/ { isf = 1; next }
           isf && /DW_AT_frame_base/ {
             found = index($0, "(DW_OP_call_frame_cfa; DW_OP_consts: " n "; DW_OP_plus)")
             exit
           }
           END { exit !found }'; then
  unsuitable_environment "$0" \
      "the frame base of cfa_offset is not DW_OP_call_frame_cfa + ${offset}"
fi

decls="${output_dir}/frame-base-cfa-offset.decls"
dtrace="${output_dir}/frame-base-cfa-offset.dtrace"
status=0
"${valgrind}" --tool=fjalar \
              --decls-file="${decls}" --dtrace-file="${dtrace}" \
              "${output_dir}/frame-base-cfa-offset" \
              > "${output_dir}/frame-base-cfa-offset.out" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  cat "${output_dir}/frame-base-cfa-offset.out" >&2
  exit 1
fi

# One line per formal parameter at cfa_offset's program points:
# "<ppt> <parameter> <value>".
actual="${output_dir}/frame-base-cfa-offset.actual"
awk '/^\.\.cfa_offset\(\):::/ { ppt = $0; next }
     /^$/ { ppt = ""; next }
     ppt != "" && ($0 == "a" || $0 == "d") { name = $0; getline; print ppt, name, $0 }' \
    "${dtrace}" > "${actual}"

if ! diff -u "${test_dir}/frame-base-cfa-offset.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from frame-base-cfa-offset.goal" >&2
  exit 1
fi

echo "$0: PASSED"
