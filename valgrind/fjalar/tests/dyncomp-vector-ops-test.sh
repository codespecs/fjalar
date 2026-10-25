#!/bin/bash

# Tests that DynComp instruments the IROps that VEX translates AVX2, FMA, and
# F16C instructions to, without panicking on an IROp that it does not handle.
# dyncomp-op-coverage-test.sh checks that dyncomp_translate.c has a case for
# each IROp; this test checks that those cases run without error.
#
# The test also checks the IR of the test program, so that it is not vacuous:
# the IR must contain each IROp in required_ops.

set -e

# One IROp per kind of instruction that dyncomp-vector-ops.c executes.
required_ops=(Add32x8 Mul32x8 Perm32x8 CmpGT32Sx8 64x4toV256
              PwExtUSMulQAdd8x16 MAddF64 Max64Fx4 Sqrt64Fx4
              F16toF32x8 Div32Fx8)

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"
program=dyncomp-vector-ops

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

# Fails in continuous integration (GitHub Actions sets CI, and Azure Pipelines
# sets TF_BUILD), and otherwise skips this test, because this CPU cannot run
# it.  Failing in continuous integration ensures that a change of machines
# that makes this test vacuous does not go unnoticed.  $1 is the reason.
unsuitable_cpu() {
  if [ -n "${CI:-}" ] || [ -n "${TF_BUILD:-}" ]; then
    echo "$0: FAILED: $1" >&2
    exit 1
  fi
  echo "$0: SKIPPED: $1" >&2
  exit 0
}

for feature in avx2 fma f16c; do
  if ! grep -qw "${feature}" /proc/cpuinfo; then
    unsuitable_cpu "the CPU does not support ${feature}"
  fi
done

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

# Fjalar does not read DWARF 5, and it recognizes a function's entry point
# only at the address in the debugging information, so the executable must not
# be position-independent.  x86-64-v3 includes AVX2, FMA, and F16C, but not
# AVX-512, which Valgrind cannot decode.
gcc -gdwarf-4 -no-pie -O2 -march=x86-64-v3 \
    -o "${output_dir}/${program}" "${test_dir}/${program}.c"

out="${output_dir}/${program}.out"
status=0
"${valgrind}" --tool=fjalar --dyncomp \
              --trace-flags=01000000 --trace-notbelow=0 \
              --decls-only --decls-file="${output_dir}/${program}.decls" \
              "${output_dir}/${program}" > "${out}" 2>&1 || status=$?

if [ "${status}" -ne 0 ]; then
  echo "$0: FAILED: Fjalar exited with status ${status}" >&2
  tail -n 100 "${out}" >&2
  exit 1
fi

# The IROps in the IR of the test program's own code.
actual_ops=$(awk -v prog="${output_dir}/${program}+" \
                 '/^==== SB / { inProg = (index($0, prog) > 0) }
                  inProg' "${out}" \
               | grep -oE '\b[A-Za-z0-9_]+\(' | tr -d '(' | sort -u)

missing=()
for op in "${required_ops[@]}"; do
  if ! grep -qx "${op}" <<< "${actual_ops}"; then
    missing+=("${op}")
  fi
done
if [ ${#missing[@]} -ne 0 ]; then
  echo "$0: FAILED: the IR of ${program} does not contain these IROps: ${missing[*]}" >&2
  exit 1
fi

echo "$0: PASSED"
