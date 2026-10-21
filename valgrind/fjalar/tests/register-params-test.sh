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

# Fails in continuous integration (GitHub Actions sets CI, and Azure Pipelines
# sets TF_BUILD), and otherwise skips this test, because this compiler cannot
# run it.  Failing in continuous integration ensures that a compiler change
# that makes this test vacuous does not go unnoticed.  $1 is the reason.
unsuitable_compiler() {
  if [ -n "${CI:-}" ] || [ -n "${TF_BUILD:-}" ]; then
    echo "$0: FAILED: $1" >&2
    exit 1
  fi
  echo "$0: SKIPPED: $1" >&2
  exit 0
}

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
if ! awk '/DW_AT_name/ && /"v\\0"/ && !done { state = 1 }
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
    "${output_dir}/stack-params.s" > "${output_dir}/stack-params-patched.s"
then
  unsuitable_compiler "could not rewrite the location of stack_value's v"
fi
gcc -gdwarf-4 -no-pie -o "${output_dir}/register-params" \
    "${output_dir}/register-params.o" "${output_dir}/stack-params-patched.s"

# register-params.goal assumes that the location of every formal parameter of
# an optimized function is a register throughout its function.  Another
# compiler version might instead use a location list, DW_OP_entry_value, or a
# constant, or might omit the location, for which Fjalar omits the formal
# parameter.  A line that starts with "<depth><offset>:" begins a new
# debugging information entry.
if readelf --debug-dump=info "${output_dir}/register-params" \
    | awk 'function end_param() { if (inparam && !hasloc) bad = 1; inparam = 0 }
           /^ *<[0-9]+><[0-9a-f]+>:/ { end_param() }
           /DW_TAG_subprogram/ { insub = 1; next }
           insub && /DW_AT_name/ { fname = $NF; insub = 0 }
           # These functions are in stack-params.c, which is not optimized.
           fname ~ /^(stack_value|kept)$/ { next }
           /DW_TAG_formal_parameter/ { inparam = 1; hasloc = 0; next }
           inparam && /DW_AT_location/ { hasloc = 1 }
           inparam && /DW_AT_location/ && !/: [0-9]+ byte block: .*\(DW_OP_reg/ { bad = 1 }
           inparam && /DW_AT_const_value/ { bad = 1 }
           END { end_param(); exit !bad }'; then
  readelf --debug-dump=info "${output_dir}/register-params" \
    | grep -A8 DW_TAG_formal_parameter >&2
  unsuitable_compiler "gcc did not put every formal parameter in a register"
fi

# A formal parameter in a register occupies no stack slot, even if Fjalar
# cannot read the register (split's p and identity's d).  Otherwise, Fjalar
# would compute a wrong stack offset for each later formal parameter that
# needs one.  The XML output gives each formal parameter's stack offset, if
# any.
xml="${output_dir}/register-params.xml"
status=0
"${valgrind}" --tool=fjalar --xml-output-file="${xml}" \
              "${output_dir}/register-params" \
              > "${output_dir}/register-params-xml.out" 2>&1 || status=$?
if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status} writing XML" >&2
  cat "${output_dir}/register-params-xml.out" >&2
  exit 1
fi
stack_slots=$(awk '/^<function>/ { getline; fname = $0 }
                   /^<formal-parameters>/ { inparams = 1 }
                   /^<\/formal-parameters>/ { inparams = 0 }
                   inparams && /^<name>/ { pname = $0 }
                   inparams && /^<stack-byte-offset>/ \
                     && fname ~ /\[(add|scale|split|identity)\]/ {
                     print fname, pname, $0 }' "${xml}")
if [ -n "${stack_slots}" ]; then
  echo "$0: FAILED: a formal parameter in a register has a stack offset:" >&2
  echo "${stack_slots}" >&2
  exit 1
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
