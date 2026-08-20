#!/bin/bash

# Tests that Fjalar traces a C compilation unit whose name starts with
# "library/".
#
# Fjalar suppresses the program points of the Rust runtime library, whose
# compilation units are named "library/..." or "/rust/deps/...".  A C or C++
# compilation unit may have such a name too, so the test must also consider
# the compilation unit's language.  Without that consideration, every function
# in library/example.c is omitted from the .decls and .dtrace files.

set -e

test_dir="$(cd "$(dirname "$0")" && pwd)"
valgrind="${test_dir}/../../inst/bin/valgrind"

if [ ! -x "${valgrind}" ]; then
  echo "$0: Fjalar is not built; run \"make build\" at the top level." >&2
  exit 2
fi

output_dir="$(mktemp -d)"
trap 'rm -rf "${output_dir}"' EXIT

# Compile with a relative path, so that DW_AT_name is "library/example.c"
# rather than an absolute path.
cd "${test_dir}"
gcc -gdwarf-4 -o "${output_dir}/example" library/example.c

decls="${output_dir}/example.decls"
"${valgrind}" --tool=fjalar --decls-only --decls-file="${decls}" \
              "${output_dir}/example" > "${output_dir}/example.out" 2>&1

if ! grep -q '^ppt \.\.addOne():::ENTER$' "${decls}"; then
  echo "$0: FAILED: no program point for addOne() in ${decls}" >&2
  echo "Fjalar treated the C compilation unit library/example.c as part of" >&2
  echo "the Rust runtime library." >&2
  cat "${output_dir}/example.out" >&2
  exit 1
fi

echo "$0: PASSED"
