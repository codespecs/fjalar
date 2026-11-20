#!/bin/bash

# Tests that Fjalar computes the frame base of a function whose frame base is
# (DW_OP_call_frame_cfa; DW_OP_consts N; DW_OP_plus), and that it rejects other
# expressions of the same length.
#
# The Rust compiler emits that expression, with a negative N, but GCC emits a
# bare DW_OP_call_frame_cfa, so the test rewrites GCC's debugging information.
# It replaces cfa_offset's frame base with the three-operation form and
# subtracts N from every DW_OP_fbreg offset, which leaves each variable at the
# same address.  So Fjalar reads the formal parameters correctly only if it
# adds the expression's constant to the CFA.  Without that, Fjalar falls back
# on the frame pointer register, which is 16 bytes below the CFA, and reads
# the wrong stack slots.
#
# The test runs these cases; each line of the goal file starts with the
# case's name:
#   exprloc-consts-8   an exprloc frame base, N = -8 (the sign rustc uses)
#   exprloc-consts16   an exprloc frame base, N = 16
#   loclist-consts-8   a location-list frame base, every entry of which is
#                      rewritten to the expression, N = -8
#   exprloc-constu16   (DW_OP_call_frame_cfa; DW_OP_constu 16; DW_OP_plus),
#                      which Fjalar does not interpret.  The test checks only
#                      that Fjalar records no frame base, not the parameters'
#                      values, which are then unpredictable.
# For every case the goal also records the frame base that Fjalar harvested,
# from the --fjalar-debug output.  For the loclist case that is DW_OP_list
# (0xe1), because Fjalar chooses the list's entry when the function is
# entered.
#
# In the exprloc cases, rewriting must not change the size of .debug_info,
# because GCC emits the compilation unit's length and its DW_AT_type and
# DW_AT_sibling offsets as literals.  The frame base grows by three bytes, and
# shortening two inline names pays for them; see frame-base-cfa-offset.c.  The
# shortened names move only the formal parameter entries, which nothing refers
# to.  In the loclist case the frame base is in .debug_loc, which GCC addresses
# by labels, so the size of .debug_info does not change and the names stay.

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

# Fjalar does not read DWARF 5, and it recognizes a function's entry point only
# at the address in the debugging information, so the executable must not be
# position-independent.  -gno-variable-location-views keeps location view pairs
# out of the .debug_loc section.  Strict DWARF 2 has no DW_OP_call_frame_cfa,
# so GCC describes the frame base as a location list.
gcc -gdwarf-4 -gno-variable-location-views -no-pie -O0 -S -dA \
    -o "${output_dir}/exprloc.s" "${test_dir}/frame-base-cfa-offset.c"
gcc -gdwarf-2 -gstrict-dwarf -no-pie -O0 -S -dA \
    -o "${output_dir}/loclist.s" "${test_dir}/frame-base-cfa-offset.c"

actual="${output_dir}/frame-base-cfa-offset.actual"
: > "${actual}"

# Builds and runs one case, and appends its results to ${actual}.
#   $1  the case's name
#   $2  "exprloc" or "loclist": the form of cfa_offset's frame base
#   $3  "consts" or "constu": the operation that pushes the constant
#   $4  the constant N
run_case() {
  local name="$1" mode="$2" const_op="$3" offset="$4"
  local exe="${output_dir}/${name}"

  # The frame pointer register is CFA - 16, so with N = -16 the test could not
  # tell the frame base from the fallback.
  if [ "${offset}" -eq -16 ]; then
    echo "$0: ${name}: N must not be -16" >&2
    exit 1
  fi

  # Rewrites cfa_offset's frame base and shifts every DW_OP_fbreg offset.  Both
  # the old and the new offset must encode as a one-byte SLEB128, or
  # .debug_info would change size.
  if ! awk -v mode="${mode}" -v const_op="${const_op}" -v n="${offset}" '
      function print_expression() {
        print "\t.byte\t0x9c\t# DW_OP_call_frame_cfa"
        if (const_op == "consts") {
          print "\t.byte\t0x11\t# DW_OP_consts"
          print "\t.sleb128 " n
        } else {
          print "\t.byte\t0x10\t# DW_OP_constu"
          print "\t.uleb128 " n
        }
        print "\t.byte\t0x22\t# DW_OP_plus"
        framebase++
      }
      function fail(message) {
        print message > "/dev/stderr"
        failed = 1
        exit 1
      }
      mode == "exprloc" && /# DW_AT_frame_base$/ {
        if ($1 != ".uleb128" || $2 != "0x1") {
          fail("unexpected frame base: " $0)
        }
        getline op
        if (op !~ /# DW_OP_call_frame_cfa$/) {
          fail("unexpected frame base operation: " op)
        }
        print "\t.uleb128 0x4\t# DW_AT_frame_base"
        print_expression()
        next
      }
      mode == "exprloc" && /# DW_AT_name$/ && index($0, "\"abc\\0\"") {
        print "\t.ascii \"a\\0\"\t# DW_AT_name"; abc++; next
      }
      mode == "exprloc" && /# DW_AT_name$/ && index($0, "\"de\\0\"") {
        print "\t.ascii \"d\\0\"\t# DW_AT_name"; de++; next
      }
      # Each entry of the location list is a DW_OP_breg6 or DW_OP_breg7 that
      # computes the CFA at its addresses.
      mode == "loclist" && /# Location expression size$/ {
        if ($2 != "0x2") {
          fail("unexpected location expression size: " $0)
        }
        getline op
        getline operand
        if (op !~ /# DW_OP_breg[67]$/ || operand !~ /^\t\.sleb128 /) {
          fail("unexpected location expression: " op " " operand)
        }
        print "\t.value\t0x4\t# Location expression size"
        print_expression()
        next
      }
      /# DW_OP_fbreg$/ {
        print
        getline operand
        split(operand, field, " ")
        if (field[1] != ".sleb128") {
          fail("unexpected fbreg operand: " operand)
        }
        old = field[2] + 0; new = old - n
        if (old < -64 || old > 63 || new < -64 || new > 63) {
          fail("fbreg offset " old " -> " new " needs more than one byte")
        }
        print "\t.sleb128 " new
        fbreg++
        next
      }
      { print }
      END {
        if (failed) {
          exit 1
        }
        if (mode == "exprloc" && (framebase != 1 || abc != 1 || de != 1)) {
          bad = 1
        }
        if (mode == "loclist" && framebase < 1) {
          bad = 1
        }
        if (bad || fbreg < 2) {
          print "rewrote frame bases: " framebase+0 ", names: " abc+0 " " de+0 \
                ", fbreg offsets: " fbreg+0 > "/dev/stderr"
          exit 1
        }
      }' "${output_dir}/${mode}.s" > "${exe}.s"; then
    unsuitable_environment "$0" "${name}: could not rewrite cfa_offset's frame base"
  fi

  gcc -no-pie -o "${exe}" "${exe}.s" "${test_dir}/frame-base-cfa-offset-main.c"

  # The rewrite must have produced the expression under test, and readelf must
  # still be able to read the debugging information around it.
  local expression
  if [ "${const_op}" = consts ]; then
    expression="(DW_OP_call_frame_cfa; DW_OP_consts: ${offset}; DW_OP_plus)"
  else
    expression="(DW_OP_call_frame_cfa; DW_OP_constu: ${offset}; DW_OP_plus)"
  fi
  if [ "${mode}" = exprloc ]; then
    if ! readelf --debug-dump=info "${exe}" 2>&1 \
        | awk -v expression="${expression}" \
              '/DW_TAG_/ { insub = /DW_TAG_subprogram/; isf = 0; next }
               insub && /DW_AT_name.*: cfa_offset$/ { isf = 1; next }
               isf && /DW_AT_frame_base/ { found = index($0, expression); exit }
               END { exit !found }'; then
      unsuitable_environment "$0" \
          "${name}: the frame base of cfa_offset is not ${expression}"
    fi
  else
    if ! readelf --debug-dump=loc "${exe}" 2>&1 | grep -qF "${expression}"; then
      unsuitable_environment "$0" \
          "${name}: the frame base location list does not contain ${expression}"
    fi
  fi

  local status=0
  "${valgrind}" --tool=fjalar --fjalar-debug \
                --decls-file="${exe}.decls" --dtrace-file="${exe}.dtrace" \
                "${exe}" > "${exe}.out" 2>&1 || status=$?

  if [ "${status}" -ne 0 ]; then
    echo "$0: FAILED: ${name}: Fjalar exited with status ${status}" >&2
    cat "${exe}.out" >&2
    exit 1
  fi

  # The frame base that Fjalar harvested for cfa_offset:
  # "<case> frame_base_atom: <atom>, frame_base_offset: <offset>".
  # enter_function prints it before the function's name.
  awk -v name="${name}" \
      '/^frame_base_atom:/ { frame_base = $0; next }
       /Enter function: \.\.cfa_offset\(\)/ { print name, frame_base; exit }' \
      "${exe}.out" >> "${actual}"

  # One line per formal parameter at cfa_offset's program points:
  # "<case> <ppt> <parameter> <value>".
  if [ "${const_op}" = consts ]; then
    awk -v name="${name}" \
        '/^\.\.cfa_offset\(\):::/ { ppt = $0; next }
         /^$/ { ppt = ""; next }
         ppt != "" && /^(a|abc|d|de)$/ { param = $0; getline; print name, ppt, param, $0 }' \
        "${exe}.dtrace" >> "${actual}"
  fi
}

run_case exprloc-consts-8 exprloc consts -8
run_case exprloc-consts16 exprloc consts 16
run_case loclist-consts-8 loclist consts -8
run_case exprloc-constu16 exprloc constu 16

if ! diff -u "${test_dir}/frame-base-cfa-offset.goal" "${actual}" >&2; then
  echo "$0: FAILED: output differs from frame-base-cfa-offset.goal" >&2
  exit 1
fi

echo "$0: PASSED"
