#!/bin/bash

# This script runs the Valgrind regression tests ("make regtest") on the
# upstream Valgrind release that is being merged into Fjalar, and records
# the tests that fail.  After the merge, a test that fails in Fjalar's tree
# and is also in that list is an upstream failure, not a bug in the merge.
# See doc/valgrind-merge.texinfo.
#
# Usage: ./upstream-regtest.sh OUTFILE
# VNEWTAG must be set, and $INV/valgrind-new must be at that tag.
#   OUTFILE is the file to write the list of failing tests to, in the
#   expected-failures format that check-regtest.sh describes.  The script
#   replaces any earlier OUTFILE, unless the tests did not run.  OUTFILE
#   may not be in $INV/valgrind-new or $INV/valgrind-new-build.
#
# The script builds and tests a fresh copy of $INV/valgrind-new, in
# $INV/valgrind-new-build, replacing any earlier copy.  It never builds in
# $INV/valgrind-new itself, so that $INV/valgrind-new stays a clean clone,
# which becomes valgrind-old for the next merge.  The test output is in
# $INV/valgrind-new-build/test.log and test-post.log.  The tests take about
# 15 minutes.
#
# Many of the gdbserver tests fail unless gdb and the glibc debuginfo
# package are installed.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

# Make "cd" with a relative directory resolve it against the current
# directory, as "git -C" does.
unset CDPATH

if [ $# -ne 1 ]; then
  echo "Usage: $0 OUTFILE" >&2
  exit 2
fi
OUTFILE=$(realpath -m "$1")

FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"
source "$FJALARDIR/valgrind-common.sh"

if [ -z "$INV" ]; then
  echo "$0: INV is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi
# Make INV absolute and free of symbolic links, like OUTFILE, so that the
# two can be compared.
if ! inv=$(cd "$INV" && pwd -P); then
  echo "$0: cannot change to directory $INV." >&2
  exit 1
fi
INV=$inv
check_toplevel "$INV/valgrind-new"
# At the next merge, it is easy to forget to clone the new release into
# valgrind-new, or to clone the wrong tag.  So require VNEWTAG, which
# merge-valgrind.sh checks only if it is set.
if [ -z "${VNEWTAG-}" ]; then
  echo "$0: VNEWTAG is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi
check_tag "$INV/valgrind-new" "$VNEWTAG" "the value of VNEWTAG"

# Check OUTFILE now rather than after the tests, which take 15 minutes.  The
# script deletes valgrind-new-build, and valgrind-new must stay a clean
# clone, so OUTFILE may be in neither.
case "$OUTFILE/" in
  "$INV"/valgrind-new/* | "$INV"/valgrind-new-build/*)
    echo "$0: OUTFILE must not be in $INV/valgrind-new or $INV/valgrind-new-build: $OUTFILE" >&2
    exit 2
    ;;
esac
if [ -d "$OUTFILE" ]; then
  echo "$0: OUTFILE is a directory: $OUTFILE" >&2
  exit 2
fi
if [ ! -d "$(dirname "$OUTFILE")" ] || [ ! -w "$(dirname "$OUTFILE")" ]; then
  echo "$0: $(dirname "$OUTFILE") is not a writable directory." >&2
  exit 2
fi

cd "$INV"
rm -rf valgrind-new-build
git -c advice.detachedHead=false clone -q valgrind-new valgrind-new-build
cd valgrind-new-build
echo "Building Valgrind in $INV/valgrind-new-build; the output is in build.log"
# "make regtest" uses the build in place, so there is no "make install".
# Installing into the source tree would also make upstream's post-test
# header check fail, because it does not know the installation directory.
if ! { ./autogen.sh && ./configure && make -j"$(nproc)" all; } \
       > build.log 2>&1; then
  echo "$0: the build failed; see $INV/valgrind-new-build/build.log" >&2
  exit 1
fi

# Run the tests with the same parallelism, XMLLINT setting, standard input,
# and TERM (unset) as check-regtest.sh.  Setting XMLLINT keeps
# "make check" from validating the manual, which fails without the DocBook
# DTD.  "make regtest" exits with non-zero status whenever any test fails,
# which is the usual case, so its status is ignored.  Some tests read
# standard input:  memcheck/tests/null_socket calls recvfrom() on it, which
# waits forever if standard input is a socket, so it is /dev/null.  Unless
# TERM is unset or "dumb", gdb 17 prefixes its error and warning messages
# with an emoji, which the gdbserver tests' filters do not remove.
echo "Running the regression tests; the output is in test.log and test-post.log"
(unset TERM; make -j"$(nproc)" regtest XMLLINT=xmllint-skipped-by-check-regtest) \
  < /dev/null > test.log 2>&1 || true
# -s and --no-print-directory keep make's own messages out of test-post.log,
# which check-regtest.sh reads (because its name is derived from test.log)
# as the post-test checks' error messages.
make -s --no-print-directory post-regtest-checks > test-post.log 2>&1 || true

# Start the list with only a header, which says which release and operating
# system the list is for.  With --update, check-regtest.sh keeps the header
# and appends this run's failures; it keeps nothing of an earlier OUTFILE,
# such as one from an earlier Valgrind release.  check-regtest.sh also
# writes the observed failures to test-observed.txt.  The list is written
# in valgrind-new-build and copied to OUTFILE only if check-regtest.sh
# succeeds, because a list with no failures, from tests that did not run,
# would wrongly say that every failure in Fjalar's tree is not upstream's.
# shellcheck disable=SC1091
OS_NAME=$(. /etc/os-release && echo "$PRETTY_NAME")
{
  echo "# Tests that fail in upstream Valgrind $VNEWTAG on $OS_NAME."
  echo "# See check-regtest.sh for the format.  Regenerate with upstream-regtest.sh."
  echo
} > upstream-failures.txt
"$FJALARDIR/check-regtest.sh" --log test.log --expected upstream-failures.txt --update
cp upstream-failures.txt "$OUTFILE"
echo "Wrote $OUTFILE"
