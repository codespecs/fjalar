#!/bin/bash

# Run Valgrind's regression tests ("make test", which runs "make regtest" in
# valgrind/) and compare the failing tests with the expected failures for this
# operating system.
#
# Valgrind never passes all of its own tests, and which tests fail depends on
# the operating system, on whether gdb and glibc debuginfo are installed, and
# sometimes on the CPU.  So this script does not require every test to pass.
# It fails if:
#  * a test fails that is not listed in the expected-failures file,
#  * the tests did not run (no summary line in the output, or no output from
#    the post-test checks), or
#  * the expected-failures file does not exist (unless --update is given).
# A test that is listed as an expected failure but passes produces a warning,
# not a failure; remove it from the expected-failures file.
#
# Usage: ./check-regtest.sh [--log FILE.log] [--expected FILE] [--update] [--report-only]
#   --log FILE.log   Read FILE.log (output of "make test") instead of running
#                    the tests, and read FILE-post.log (output of
#                    "make -C valgrind -s --no-print-directory post-regtest-checks")
#                    for the errors of the post-test checks.  Without --log,
#                    the script runs the tests and writes both files, as
#                    regtest-<os>.log and regtest-<os>-post.log in this
#                    directory, where <os> is computed from /etc/os-release,
#                    for example "ubuntu-26.04" or "rocky-10".
#   --expected FILE  Use FILE as the expected-failures file.  The default is
#                    regtest-expected/<os>.txt.
#   --update         Rewrite the expected-failures file to match this run:
#                    remove entries that did not fail and append new failures.
#                    Blank lines and "?" lines are kept in place.  Comment
#                    lines are kept in place, except that comment lines
#                    directly above a group of entries (lines with no blank
#                    line between them) are removed if every entry in the
#                    group is removed.  Review the diff!
#   --report-only    Report differences, but exit with status 0 even if there
#                    are unexpected failures or there is no expected-failures
#                    file.  It still exits with non-zero status if the tests
#                    did not run.
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
#  * "TEST (post check failed)", such as
#    "massif/tests/big-alloc (post check failed)", means that the "post:"
#    command of the test failed to run.
#
# Whatever the outcome, the observed failures are written to FILE-observed.txt
# (next to FILE.log), so that CI can save them.

# Fail the whole script if any command fails.
set -e
set -o pipefail
# sort and comm run with LC_ALL=C, so that they order lines the same way on
# every machine.  The tests themselves run in the caller's locale, as the
# upstream baseline in plan-upgrade-valgrind.md does.

# Resolve symbolic links, so that paths that are compared with each other
# (such as $EXPECTED_FILE, which goes through realpath) are in the same form.
FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"

LOG_FILE=
EXPECTED_FILE=
UPDATE=false
REPORT_ONLY=false
# Exit with a usage error if option $1 lacks a non-empty argument $2.
require_option_argument() {
  if [ -z "$2" ]; then
    echo "$0: $1 requires an argument" >&2
    exit 2
  fi
}
while [ $# -gt 0 ]; do
  case "$1" in
    --log) require_option_argument "$1" "${2-}"; LOG_FILE="$2"; shift 2 ;;
    --expected) require_option_argument "$1" "${2-}"; EXPECTED_FILE="$2"; shift 2 ;;
    --update) UPDATE=true; shift ;;
    --report-only) REPORT_ONLY=true; shift ;;
    *) echo "$0: unknown argument: $1" >&2; exit 2 ;;
  esac
done
if [ -n "$LOG_FILE" ] && [ "${LOG_FILE%.log}" = "$LOG_FILE" ]; then
  echo "$0: --log file name must end in .log: $LOG_FILE" >&2
  exit 2
fi
# Make file arguments absolute before changing directory.
[ -n "$LOG_FILE" ] && LOG_FILE="$(realpath -m "$LOG_FILE")"
[ -n "$EXPECTED_FILE" ] && EXPECTED_FILE="$(realpath -m "$EXPECTED_FILE")"
# A missing log means a mistyped --log or a run that never happened.
if [ -n "$LOG_FILE" ]; then
  for f in "$LOG_FILE" "${LOG_FILE%.log}-post.log"; do
    if [ ! -f "$f" ]; then
      echo "$0: no such file: $f" >&2
      exit 2
    fi
  done
fi
cd "$FJALARDIR"

# The operating system name, such as "ubuntu-26.04" or "rocky-10".  For
# RHEL-like distributions, use only the major version, because minor releases
# (10.0, 10.1, ...) are routine updates of the same distribution.  A
# rolling-release distribution (such as Arch or Debian sid) has no VERSION_ID;
# use only its ID.
os_name() {
  if [ ! -f /etc/os-release ]; then
    echo "$0: /etc/os-release does not exist; cannot determine the operating system" >&2
    exit 2
  fi
  # shellcheck disable=SC1091
  . /etc/os-release
  if [ -z "${VERSION_ID-}" ]; then
    echo "$ID"
    return
  fi
  case "$ID" in
    rocky|rhel|almalinux|centos|fedora) echo "$ID-${VERSION_ID%%.*}" ;;
    *) echo "$ID-$VERSION_ID" ;;
  esac
}
OS="$(os_name)"
EXPECTED_FILE="${EXPECTED_FILE:-$FJALARDIR/regtest-expected/$OS.txt}"

RUN_TESTS=false
if [ -z "$LOG_FILE" ]; then
  RUN_TESTS=true
  LOG_FILE="$FJALARDIR/regtest-$OS.log"
fi
POSTLOG_FILE="${LOG_FILE%.log}-post.log"
OBSERVED_FILE="${LOG_FILE%.log}-observed.txt"

if [ "$RUN_TESTS" = true ]; then
  echo "Running Valgrind regression tests; output is in $LOG_FILE and $POSTLOG_FILE"
  # "make regtest" exits with non-zero status whenever any test fails, which
  # is the usual case, so ignore its status and examine its output instead.
  # "make regtest" first runs "make check", which also validates Valgrind's XML
  # manual with xmllint if xmllint is installed.  That needs the DocBook DTD,
  # from a package or the network, and is not a test of Valgrind's behavior.
  # Naming a nonexistent xmllint makes docs/Makefile skip the validation.
  # -j speeds up "make check", which builds about a thousand test programs.
  # It does not affect vg_regtest, which runs the tests serially.
  make -j"$(nproc)" test XMLLINT=xmllint-skipped-by-check-regtest > "$LOG_FILE" 2>&1 || true
  # "make test" ends by running the post-test checks, but in $LOG_FILE their
  # error messages are mixed with make's output.  Run them again by themselves.
  make -C valgrind -s --no-print-directory post-regtest-checks > "$POSTLOG_FILE" 2>&1 || true
fi

# The summary line has this form:
#   == 809 tests, 0 stderr failures, 0 stdout failures, 2 stderrB failures, 16 stdoutB failures, 0 post failures ==
# It is followed by one line per failure, then a blank line.
SUMMARY_RE='^== [0-9]+ tests?, .* post failures? ==$'

# Collapse each run of whitespace to one space, and remove leading and
# trailing whitespace.  Observed and expected entries are compared in this
# form, so that differences in whitespace do not matter.
normalize_whitespace() {
  sed -E 's/[[:space:]]+/ /g; s/^ //; s/ $//'
}

# Print the observed failures, one per line, normalized to "name (kind)".
print_observed_failures() {
  awk -v summary_re="$SUMMARY_RE" '
    $0 ~ summary_re { in_summary = 1; next }
    in_summary && /^[ \t]*$/ { in_summary = 0; next }
    in_summary { failures[n++] = $0; next }
    # Track the directory and name of the test that is running, such as
    #   -- Running  tests in massif/tests ------------------------------
    #   big-alloc:       valgrind --stacks=no ./big-alloc
    # vg_regtest recurses into subdirectories, such as none/tests/ppc64, and
    # then continues with the parent directory, so keep a stack.
    /^-- Running  tests in / { dirs[++depth] = $5; dir = $5; next }
    /^-- Finished tests in / { if (depth > 0) depth--; dir = dirs[depth]; next }
    /^[^ :]+: +valgrind / { test = substr($1, 1, length($1) - 1); next }
    # The "post:" command of the test failed to run.  vg_regtest counts this
    # in the summary line but does not list it.
    /^post check failed: / { failures[n++] = dir "/" test " (post check failed)"; next }
    END { for (i = 0; i < n; i++) print failures[i] }' "$LOG_FILE"
  # The error messages of tests/post_regtest_checks: every line of
  # $POSTLOG_FILE except its progress messages, make's messages, and blank
  # lines.
  { grep -Ev '^(\.\.\.checking |make(\[[0-9]+\])?: |[^ :]*[Mm]akefile:[0-9]+: recipe for target |[[:space:]]*$)' "$POSTLOG_FILE" || true; } \
    | sed 's/^/post_regtest_checks: /'
}
print_observed_failures | normalize_whitespace | LC_ALL=C sort -u > "$OBSERVED_FILE"

# A summary that reports 0 tests means that no test ran.  This is an error
# even with --report-only, because it means that nothing was checked.
NONZERO_SUMMARY_RE='^== [1-9][0-9]* tests?, .* post failures? ==$'
if ! grep -Eq "$NONZERO_SUMMARY_RE" "$LOG_FILE"; then
  echo "$0: no regtest summary line with a nonzero test count in $LOG_FILE; the tests did not run." >&2
  echo "Last lines of $LOG_FILE:" >&2
  tail -n 40 "$LOG_FILE" >&2
  exit 1
fi
# The last of the post-test checks prints this progress message.
if ! grep -q '^\.\.\.checking header files and include directives' "$POSTLOG_FILE"; then
  echo "$0: the post-test checks did not run; output is in $POSTLOG_FILE:" >&2
  tail -n 40 "$POSTLOG_FILE" >&2
  exit 1
fi
grep -E "$SUMMARY_RE" "$LOG_FILE" | tail -n 1

# The entries of the expected-failures file: REQUIRED (without comments,
# blank lines, or "?" lines), OPTIONAL (the "?" lines, without the "?"),
# and ALLOWED (both).  The file is absent for an OS or an --expected path
# that has no expected failures recorded yet; then every failure is unexpected.
if [ -f "$EXPECTED_FILE" ]; then
  REQUIRED="$({ grep -Ev '^[[:space:]]*(#|\?|$)' "$EXPECTED_FILE" || true; } | normalize_whitespace | LC_ALL=C sort -u)"
  OPTIONAL="$({ grep -E '^[[:space:]]*\?' "$EXPECTED_FILE" || true; } \
    | sed -E 's/^[[:space:]]*\?//' | normalize_whitespace | LC_ALL=C sort -u)"
else
  REQUIRED=
  OPTIONAL=
fi
ALLOWED="$(printf '%s\n%s\n' "$REQUIRED" "$OPTIONAL" | grep -v '^$' | LC_ALL=C sort -u || true)"

UNEXPECTED="$(LC_ALL=C comm -23 "$OBSERVED_FILE" <(echo "$ALLOWED") | grep -v '^$' || true)"
NEWLY_PASSING="$(LC_ALL=C comm -13 "$OBSERVED_FILE" <(echo "$REQUIRED") | grep -v '^$' || true)"

if [ "$UPDATE" = true ]; then
  mkdir -p "$(dirname "$EXPECTED_FILE")"
  TMP_FILE="$(mktemp)"
  trap 'rm -f "$TMP_FILE"' EXIT
  # Update the existing file, or create a new one with a header.
  if [ -f "$EXPECTED_FILE" ]; then
    # Keep comments, blank lines, "?" lines, and the required entries that
    # failed, in their original order (the file is not sorted), so that a
    # comment stays next to the entries that it explains.  A group is the
    # comment lines directly above some entries plus those entries.  A kept
    # entry is a "?" line or a required entry that failed in this run.  The
    # group's comment lines are printed when its first kept entry is, and are
    # dropped if it has none.  Consecutive blank lines are collapsed, because
    # dropping a group can leave two blank lines next to each other.
    # The awk input is each line of $EXPECTED_FILE, normalized, then a tab
    # (which a normalized line does not contain), then the line itself.
    # The test is not "NR == FNR", which would be true for every line of
    # $EXPECTED_FILE if $OBSERVED_FILE were empty.
    paste <(normalize_whitespace < "$EXPECTED_FILE") "$EXPECTED_FILE" \
      | awk -F '\t' 'function flush() { printf "%s", held; held = "" }
         function out(s) { flush(); print s; last_blank = (s ~ /^[[:space:]]*$/) }
         FILENAME == ARGV[1] { observed[$0] = 1; next }
         { entry = $1; line = substr($0, length($1) + 2) }
         entry ~ /^#/ { if (in_group) { held = ""; in_group = 0 }
                        held = held line "\n"; next }
         entry == "" { if (in_group) held = ""; in_group = 0
                       if (held != "" || !last_blank) out(line); next }
         entry ~ /^\?/ { in_group = 1; out(line); next }
         { in_group = 1; if (entry in observed) out(line) }
         END { if (!in_group) flush() }' \
      "$OBSERVED_FILE" - > "$TMP_FILE"
  else
    {
      echo "# Expected failures of Valgrind's regression tests (\"make regtest\") on $OS."
      echo "# See check-regtest.sh for the format.  Regenerate with:"
      if [ "$EXPECTED_FILE" = "$FJALARDIR/regtest-expected/$OS.txt" ]; then
        echo "#   ./check-regtest.sh --update"
      else
        echo "#   check-regtest.sh --log <output of \"make regtest\"> --expected <this file> --update"
      fi
      # Separate the header from the entries, so that removing every entry
      # does not remove the header too.
      echo
    } > "$TMP_FILE"
  fi
  # Append the observed failures that are not already listed.  Separate them
  # from a comment at the end of the file, so that the comment does not
  # appear to explain them.
  if [ -n "$UNEXPECTED" ]; then
    if [ -n "$(tail -n 1 "$TMP_FILE" | tr -d '[:space:]')" ]; then
      echo >> "$TMP_FILE"
    fi
    echo "$UNEXPECTED" >> "$TMP_FILE"
  fi
  # Overwrite rather than move, so that the file keeps its permissions
  # (or, if new, gets the default ones rather than mktemp's 0600).
  cat "$TMP_FILE" > "$EXPECTED_FILE"
  echo "Updated $EXPECTED_FILE; review the diff before committing it."
  exit 0
fi

# No expected failures are recorded yet for this OS or --expected path.
if [ ! -f "$EXPECTED_FILE" ]; then
  echo "$0: no expected-failures file $EXPECTED_FILE." >&2
  echo "The observed failures (also in $OBSERVED_FILE) are:" >&2
  cat "$OBSERVED_FILE" >&2
  printf 'To create it, run: %q --log %q --expected %q --update\n' \
    "$0" "$LOG_FILE" "$EXPECTED_FILE" >&2
  [ "$REPORT_ONLY" = true ] && exit 0
  exit 1
fi

# Print each line of the argument, indented.
indent_each_line() {
  while IFS= read -r line; do echo "  $line"; done <<< "$1"
}

if [ -n "$NEWLY_PASSING" ]; then
  echo
  echo "Warning: these tests are listed in $EXPECTED_FILE but did not fail:"
  indent_each_line "$NEWLY_PASSING"
  echo "Remove them from $EXPECTED_FILE, or mark them with \"?\" if they fail only sometimes."
fi

if [ -n "$UNEXPECTED" ]; then
  echo
  echo "Error: these tests failed but are not listed in $EXPECTED_FILE:"
  indent_each_line "$UNEXPECTED"
  echo "Full output is in $LOG_FILE."
  [ "$REPORT_ONLY" = true ] && exit 0
  exit 1
fi

echo
echo "Valgrind regression tests: no unexpected failures (compared to $EXPECTED_FILE)."
