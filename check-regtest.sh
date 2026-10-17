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
# Usage: ./check-regtest.sh [--log FILE [--post-log FILE]] [--expected FILE] [--observed FILE] [--update] [--report-only]
#   --log FILE       Read FILE (output of "make test") instead of running the tests.
#   --post-log FILE  With --log, read FILE (output of
#                    "make -C valgrind post-regtest-checks") for the errors of
#                    the post-test checks.  The default is the --log file name
#                    with ".log" replaced by "-post.log".  Without --log, the
#                    script writes both files: regtest-<os>.log and
#                    regtest-<os>-post.log.
#   --expected FILE  Use FILE as the expected-failures file.  The default is
#                    regtest-expected/<os>.txt, where <os> is computed from
#                    /etc/os-release, for example "ubuntu-26.04" or "rocky-10".
#   --observed FILE  Write the observed failures to FILE.  The default is
#                    regtest-observed-<os>.txt (in this directory).
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
# Whatever the outcome, the observed failures are written to the --observed
# file, so that CI can save them.

# Fail the whole script if any command fails.
set -e
set -o pipefail
# Make sort and comm order lines the same way on every machine.
export LC_ALL=C

# Resolve symbolic links, so that paths that are compared with each other
# (such as $EXPECTED, which goes through realpath) are in the same form.
FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"

LOG=
POSTLOG=
EXPECTED=
OBSERVED=
UPDATE=false
REPORT_ONLY=false
# Exit with a usage error if option $1 lacks a non-empty argument $2.
need_arg() {
  if [ -z "$2" ]; then
    echo "$0: $1 requires an argument" >&2
    exit 2
  fi
}
while [ $# -gt 0 ]; do
  case "$1" in
    --log) need_arg "$1" "${2-}"; LOG="$2"; shift 2 ;;
    --post-log) need_arg "$1" "${2-}"; POSTLOG="$2"; shift 2 ;;
    --expected) need_arg "$1" "${2-}"; EXPECTED="$2"; shift 2 ;;
    --observed) need_arg "$1" "${2-}"; OBSERVED="$2"; shift 2 ;;
    --update) UPDATE=true; shift ;;
    --report-only) REPORT_ONLY=true; shift ;;
    *) echo "$0: unknown argument: $1" >&2; exit 2 ;;
  esac
done
# Make file arguments absolute before changing directory.
if [ -n "$POSTLOG" ] && [ -z "$LOG" ]; then
  echo "$0: --post-log requires --log" >&2
  exit 2
fi
[ -n "$LOG" ] && LOG="$(realpath -m "$LOG")"
[ -n "$LOG" ] && POSTLOG="$(realpath -m "${POSTLOG:-${LOG%.log}-post.log}")"
[ -n "$EXPECTED" ] && EXPECTED="$(realpath -m "$EXPECTED")"
[ -n "$OBSERVED" ] && OBSERVED="$(realpath -m "$OBSERVED")"
for f in "$LOG" "$POSTLOG"; do
  if [ -n "$f" ] && [ ! -f "$f" ]; then
    echo "$0: no such file: $f" >&2
    exit 2
  fi
done
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
EXPECTED="${EXPECTED:-$FJALARDIR/regtest-expected/$OS.txt}"
OBSERVED="${OBSERVED:-$FJALARDIR/regtest-observed-$OS.txt}"

if [ -z "$LOG" ]; then
  LOG="$FJALARDIR/regtest-$OS.log"
  POSTLOG="$FJALARDIR/regtest-$OS-post.log"
  echo "Running Valgrind regression tests; output is in $LOG and $POSTLOG"
  # "make regtest" exits with non-zero status whenever any test fails, which
  # is the usual case, so ignore its status and examine its output instead.
  # "make regtest" first runs "make check", which also validates Valgrind's XML
  # manual with xmllint if xmllint is installed.  That needs the DocBook DTD,
  # from a package or the network, and is not a test of Valgrind's behavior.
  # Naming a nonexistent xmllint makes docs/Makefile skip the validation.
  # "make check" builds about a thousand test programs; build them in
  # parallel first, because "make regtest" builds them serially.
  # vg_regtest itself runs the tests serially.
  make -C valgrind -j"$(nproc)" check XMLLINT=xmllint-skipped-by-check-regtest \
    > "$LOG" 2>&1 || true
  make test XMLLINT=xmllint-skipped-by-check-regtest >> "$LOG" 2>&1 || true
  # "make test" ends by running the post-test checks, but in $LOG their error
  # messages are mixed with make's output.  Run them again by themselves.
  make -C valgrind -s --no-print-directory post-regtest-checks > "$POSTLOG" 2>&1 || true
fi

# The summary line has this form:
#   == 809 tests, 0 stderr failures, 0 stdout failures, 2 stderrB failures, 16 stdoutB failures, 0 post failures ==
# It is followed by one line per failure, then a blank line.
SUMMARY_RE='^== [0-9]+ tests?, .* post failures? ==$'

# Collapse each run of whitespace to one space, and remove leading and
# trailing whitespace.  Observed and expected entries are compared in this
# form, so that differences in whitespace do not matter.
normalize() {
  sed -E 's/[[:space:]]+/ /g; s/^ //; s/ $//'
}

# Print the observed failures, one per line, normalized to "name (kind)".
observed_failures() {
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
    END { for (i = 0; i < n; i++) print failures[i] }' "$LOG"
  # The error messages of tests/post_regtest_checks: every line of $POSTLOG
  # except its progress messages, make's messages, and blank lines.
  { grep -Ev '^(\.\.\.checking |make(\[[0-9]+\])?: |[^ :]*[Mm]akefile:[0-9]+: recipe for target |[[:space:]]*$)' "$POSTLOG" || true; } \
    | sed 's/^/post_regtest_checks: /'
}
observed_failures | normalize | sort -u > "$OBSERVED"

# A summary that reports 0 tests means that no test ran.  This is an error
# even with --report-only, because it means that nothing was checked.
NONZERO_SUMMARY_RE='^== [1-9][0-9]* tests?, .* post failures? ==$'
if ! grep -Eq "$NONZERO_SUMMARY_RE" "$LOG"; then
  echo "$0: no regtest summary line with a nonzero test count in $LOG; the tests did not run." >&2
  echo "Last lines of $LOG:" >&2
  tail -n 40 "$LOG" >&2
  exit 1
fi
# The last of the post-test checks prints this progress message.
if ! grep -q '^\.\.\.checking header files and include directives' "$POSTLOG"; then
  echo "$0: the post-test checks did not run; output is in $POSTLOG:" >&2
  tail -n 40 "$POSTLOG" >&2
  exit 1
fi
grep -E "$SUMMARY_RE" "$LOG" | tail -n 1

# The entries of the expected-failures file: REQUIRED (without comments,
# blank lines, or "?" lines), OPTIONAL (the "?" lines, without the "?"),
# and ALLOWED (both).
if [ -f "$EXPECTED" ]; then
  REQUIRED="$({ grep -Ev '^[[:space:]]*(#|\?|$)' "$EXPECTED" || true; } | normalize | sort -u)"
  OPTIONAL="$({ grep -E '^[[:space:]]*\?' "$EXPECTED" || true; } \
    | sed -E 's/^[[:space:]]*\?//' | normalize | sort -u)"
else
  REQUIRED=
  OPTIONAL=
fi
ALLOWED="$(printf '%s\n%s\n' "$REQUIRED" "$OPTIONAL" | grep -v '^$' | sort -u || true)"

UNEXPECTED="$(comm -23 "$OBSERVED" <(echo "$ALLOWED") | grep -v '^$' || true)"
NEWLY_PASSING="$(comm -13 "$OBSERVED" <(echo "$REQUIRED") | grep -v '^$' || true)"

if [ "$UPDATE" = true ]; then
  mkdir -p "$(dirname "$EXPECTED")"
  TMP="$(mktemp)"
  trap 'rm -f "$TMP"' EXIT
  if [ -f "$EXPECTED" ]; then
    # Keep comments, blank lines, "?" lines, and the required entries that
    # failed, each in its place, so that a comment stays next to the entries
    # that it explains.  A group is the comment lines directly above some
    # entries plus those entries ("?" lines count as kept entries).  The
    # group's comment lines are printed when its first kept entry is, and are
    # dropped if it has none.  Consecutive blank lines are collapsed, because
    # dropping a group can leave two blank lines next to each other.
    # The awk input is each line of $EXPECTED, normalized, then a tab (which
    # a normalized line does not contain), then the line itself.
    # The test is not "NR == FNR", which would be true for every line of
    # $EXPECTED if $OBSERVED were empty.
    paste <(normalize < "$EXPECTED") "$EXPECTED" \
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
      "$OBSERVED" - > "$TMP"
  else
    {
      echo "# Expected failures of Valgrind's regression tests (\"make regtest\") on $OS."
      echo "# See check-regtest.sh for the format.  Regenerate with:"
      if [ "$EXPECTED" = "$FJALARDIR/regtest-expected/$OS.txt" ]; then
        echo "#   ./check-regtest.sh --update"
      else
        echo "#   check-regtest.sh --log <output of \"make regtest\"> --expected <this file> --update"
      fi
      # Separate the header from the entries, so that removing every entry
      # does not remove the header too.
      echo
    } > "$TMP"
  fi
  # Append the observed failures that are not already listed.  Separate them
  # from a comment at the end of the file, so that the comment does not
  # appear to explain them.
  if [ -n "$UNEXPECTED" ]; then
    if [ -n "$(tail -n 1 "$TMP" | tr -d '[:space:]')" ]; then
      echo >> "$TMP"
    fi
    echo "$UNEXPECTED" >> "$TMP"
  fi
  # Overwrite rather than move, so that the file keeps its permissions
  # (or, if new, gets the default ones rather than mktemp's 0600).
  cat "$TMP" > "$EXPECTED"
  echo "Updated $EXPECTED; review the diff before committing it."
  exit 0
fi

if [ ! -f "$EXPECTED" ]; then
  echo "$0: no expected-failures file $EXPECTED." >&2
  echo "The observed failures (also in $OBSERVED) are:" >&2
  cat "$OBSERVED" >&2
  printf 'To create it, run: %q --log %q --post-log %q --expected %q --observed %q --update\n' \
    "$0" "$LOG" "$POSTLOG" "$EXPECTED" "$OBSERVED" >&2
  [ "$REPORT_ONLY" = true ] && exit 0
  exit 1
fi

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
