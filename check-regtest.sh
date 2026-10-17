#!/bin/bash

# Run Valgrind's regression tests ("make test", which runs "make regtest" in
# valgrind/) and compare the failing tests with the expected failures for this
# operating system.
#
# Valgrind never passes all of its own tests, and which tests fail depends on
# the operating system, on whether gdb and glibc debuginfo are installed, and
# sometimes on the CPU.  So this script does not require every test to pass.
# It fails if:
#  * a test fails that is not listed in the expected-failures file, or
#  * the tests did not run (no summary line in the output).
# A test that is listed as an expected failure but passes produces a warning,
# not a failure; remove it from the expected-failures file.
#
# Usage: ./check-regtest.sh [--log FILE] [--expected FILE] [--update] [--report-only]
#   --log FILE       Read FILE (output of "make test") instead of running the tests.
#   --expected FILE  Use FILE as the expected-failures file.  The default is
#                    regtest-expected/<os>.txt, where <os> is computed from
#                    /etc/os-release, for example "ubuntu-26.04" or "rocky-10".
#   --update         Rewrite the expected-failures file to match this run.
#                    Comment lines and "?" lines are kept.  Review the diff!
#   --report-only    Report differences, but exit with status 0 regardless.
#
# Expected-failures file format: one failure per line, as vg_regtest prints
# it, such as "gdbserver_tests/mcleak (stdoutB)".  Blank lines and lines
# starting with "#" are ignored.  A line starting with "?" (such as
# "? helgrind/tests/tc22_exit_w_lock (stderr)") is a test that may or may not
# fail, for example because it is timing-dependent or CPU-dependent.
# Two other kinds of entry record failures that are not tied to one test:
#  * "post_regtest_checks: MESSAGE" is one error message from the checks that
#    "make regtest" runs after the tests (makefile consistency, header files
#    and include directives), such as
#    "post_regtest_checks: *** File fjalar/typedata.c must not include ../coregrind/pub_core_mallocfree.h".
#  * "post check failed: COMMAND" means that the "post:" command of a test
#    failed to run.
#
# Whatever the outcome, the observed failures are written to
# regtest-observed-<os>.txt (in this directory), so that CI can save them.

# Fail the whole script if any command fails.
set -e
set -o pipefail

FJALARDIR="$(cd "$(dirname "$0")" && pwd)"

LOG=
EXPECTED=
UPDATE=false
REPORT_ONLY=false
while [ $# -gt 0 ]; do
  case "$1" in
    --log) LOG="$2"; shift 2 ;;
    --expected) EXPECTED="$2"; shift 2 ;;
    --update) UPDATE=true; shift ;;
    --report-only) REPORT_ONLY=true; shift ;;
    *) echo "$0: unknown argument: $1" >&2; exit 2 ;;
  esac
done
# Make file arguments absolute before changing directory.
[ -n "$LOG" ] && LOG="$(realpath -m "$LOG")"
[ -n "$EXPECTED" ] && EXPECTED="$(realpath -m "$EXPECTED")"
cd "$FJALARDIR"

# The operating system name, such as "ubuntu-26.04" or "rocky-10".  For
# RHEL-like distributions, use only the major version, because minor releases
# (10.0, 10.1, ...) are routine updates of the same distribution.
os_name() {
  # shellcheck disable=SC1091
  . /etc/os-release
  case "$ID" in
    rocky|rhel|almalinux|centos|fedora) echo "$ID-${VERSION_ID%%.*}" ;;
    *) echo "$ID-$VERSION_ID" ;;
  esac
}
OS="$(os_name)"
EXPECTED="${EXPECTED:-regtest-expected/$OS.txt}"
OBSERVED="$FJALARDIR/regtest-observed-$OS.txt"

if [ -z "$LOG" ]; then
  LOG="$FJALARDIR/regtest-$OS.log"
  echo "Running Valgrind regression tests; output is in $LOG"
  # "make regtest" exits with non-zero status whenever any test fails, which
  # is the usual case, so ignore its status and examine its output instead.
  # "make regtest" first runs "make check", which also validates Valgrind's XML
  # manual with xmllint if xmllint is installed.  That needs the DocBook DTD,
  # from a package or the network, and is not a test of Valgrind's behavior.
  # Naming a nonexistent xmllint makes docs/Makefile skip the validation.
  make test XMLLINT=xmllint-skipped-by-check-regtest > "$LOG" 2>&1 || true
fi

# The summary line has this form:
#   == 809 tests, 0 stderr failures, 0 stdout failures, 2 stderrB failures, 16 stdoutB failures, 0 post failures ==
# It is followed by one line per failure, then a blank line.
SUMMARY_RE='^== [0-9]+ tests?, .* post failures? ==$'
# A summary that reports 0 tests means that no test ran.
NONZERO_SUMMARY_RE='^== [1-9][0-9]* tests?, .* post failures? ==$'
if ! grep -Eq "$NONZERO_SUMMARY_RE" "$LOG"; then
  echo "$0: no regtest summary line with a nonzero test count in $LOG; the tests did not run." >&2
  echo "Last lines of $LOG:" >&2
  tail -n 40 "$LOG" >&2
  exit 1
fi
grep -E "$SUMMARY_RE" "$LOG" | tail -n 1

# Print the observed failures, one per line, normalized to "name (kind)".
observed_failures() {
  awk -v summary_re="$SUMMARY_RE" '
    $0 ~ summary_re { in_summary = 1; next }
    in_summary && /^[ \t]*$/ { in_summary = 0; next }
    in_summary { $1 = $1; failures[n++] = $0; next }
    # A "post:" command in a .vgtest file failed to run.  vg_regtest counts
    # this in the summary line but does not list it.
    /^post check failed: / { $1 = $1; failures[n++] = $0; next }
    # Output of tests/post_regtest_checks, other than its progress messages.
    /^\.\.\.checking / { in_post_checks = 1; next }
    in_post_checks && !/^make(\[[0-9]+\])?: / && !/^[ \t]*$/ {
      $1 = $1; post_errors[m++] = "post_regtest_checks: " $0
    }
    END {
      for (i = 0; i < n; i++) print failures[i]
      for (i = 0; i < m; i++) print post_errors[i]
    }' "$LOG" | sort -u
}
observed_failures > "$OBSERVED"

# Lines of the expected-failures file, without comments, blank lines, or "?".
expected_required() {
  { grep -Ev '^[[:space:]]*(#|\?|$)' "$1" || true; } \
    | sed -E 's/[[:space:]]+/ /g; s/^ //; s/ $//' | sort -u
}
expected_optional() {
  { grep -E '^[[:space:]]*\?' "$1" || true; } \
    | sed -E 's/^[[:space:]]*\?[[:space:]]*//; s/[[:space:]]+/ /g; s/ $//' | sort -u
}

if [ "$UPDATE" = true ]; then
  mkdir -p "$(dirname "$EXPECTED")"
  TMP="$(mktemp)"
  if [ -f "$EXPECTED" ]; then
    # Keep comments and "?" lines; replace everything else.
    { grep -E '^[[:space:]]*(#|\?)' "$EXPECTED" || true; } > "$TMP"
    OPTIONAL="$(expected_optional "$EXPECTED")"
  else
    {
      echo "# Expected failures of Valgrind's regression tests (\"make test\") on $OS."
      echo "# See check-regtest.sh for the format.  Regenerate with: ./check-regtest.sh --update"
    } > "$TMP"
    OPTIONAL=
  fi
  # Required failures are those observed that are not already optional.
  comm -23 "$OBSERVED" <(echo -n "${OPTIONAL:+$OPTIONAL$'\n'}" | sort -u) >> "$TMP"
  mv "$TMP" "$EXPECTED"
  echo "Updated $EXPECTED; review the diff before committing it."
  exit 0
fi

if [ ! -f "$EXPECTED" ]; then
  echo "$0: no expected-failures file $EXPECTED." >&2
  echo "The observed failures (also in $OBSERVED) are:" >&2
  cat "$OBSERVED" >&2
  echo "To create it, run: $0 --log $LOG --update" >&2
  [ "$REPORT_ONLY" = true ] && exit 0
  exit 1
fi

REQUIRED="$(expected_required "$EXPECTED")"
OPTIONAL="$(expected_optional "$EXPECTED")"
ALLOWED="$(printf '%s\n%s\n' "$REQUIRED" "$OPTIONAL" | grep -v '^$' | sort -u || true)"

UNEXPECTED="$(comm -23 "$OBSERVED" <(echo "$ALLOWED") | grep -v '^$' || true)"
NEWLY_PASSING="$(comm -13 "$OBSERVED" <(echo "$REQUIRED") | grep -v '^$' || true)"

# Print each line of the argument, indented.
indent() {
  while IFS= read -r line; do echo "  $line"; done <<< "$1"
}

if [ -n "$NEWLY_PASSING" ]; then
  echo
  echo "Warning: these tests are listed in $EXPECTED but did not fail:"
  indent "$NEWLY_PASSING"
  echo "Remove them from $EXPECTED, or mark them with \"?\" if they fail only sometimes."
fi

if [ -n "$UNEXPECTED" ]; then
  echo
  echo "Error: these tests failed but are not listed in $EXPECTED:"
  indent "$UNEXPECTED"
  echo "Full output is in $LOG."
  [ "$REPORT_ONLY" = true ] && exit 0
  exit 1
fi

echo
echo "Valgrind regression tests: no unexpected failures (compared to $EXPECTED)."
