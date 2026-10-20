#!/bin/bash

# This script runs the Valgrind regression tests ("make regtest") on the
# upstream Valgrind release that is being merged into Fjalar, and records
# the tests that fail.  After the merge, a test that fails in Fjalar's tree
# and is also in that list is an upstream failure, not a bug in the merge.
# See doc/valgrind-merge.texinfo.
#
# Usage: ./upstream-regtest.sh OUTFILE
#   OUTFILE is the file to write the list of failing tests to, in the format
#   of regtest-expected/*.txt.
#
# The script builds and tests a fresh copy of $INV/valgrind-new, in
# $INV/valgrind-new-build, replacing any earlier copy.  It never builds in
# $INV/valgrind-new itself, which must stay a pristine clone:
# generate-patch-files.sh diffs it, and it becomes valgrind-old for the
# next merge.  The test output is in $INV/valgrind-new-build/test.log and
# test-post.log.  The tests take about 15 minutes.
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

if [ -z "$INV" ]; then
  echo "$0: INV is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi
if [ ! -d "$INV/valgrind-new/.git" ]; then
  echo "$0: $INV/valgrind-new is not a git clone." >&2
  exit 1
fi

cd "$INV"
rm -rf valgrind-new-build
git -c advice.detachedHead=false clone -q valgrind-new valgrind-new-build
cd valgrind-new-build
echo "Building Valgrind in $INV/valgrind-new-build; the output is in build.log"
# "make -j all install" would build the goals "all" and "install" in
# parallel, so that two compilations of each file could collide.
if ! { ./autogen.sh && ./configure --prefix="$(pwd)/inst" \
         && make -j"$(nproc)" all && make install; } > build.log 2>&1; then
  echo "$0: the build failed; see $INV/valgrind-new-build/build.log" >&2
  exit 1
fi

# These are the options that check-regtest.sh uses.  Setting XMLLINT keeps
# "make check" from validating the manual, which fails without the DocBook
# DTD.  "make regtest" exits with non-zero status whenever any test fails,
# which is the usual case, so its status is ignored.  Some tests read
# standard input:  memcheck/tests/null_socket calls recvfrom() on it, which
# waits forever if standard input is a socket, so it is /dev/null.
echo "Running the regression tests; the output is in test.log and test-post.log"
make -j"$(nproc)" regtest XMLLINT=xmllint-skipped-by-check-regtest \
  < /dev/null > test.log 2>&1 || true
# -s and --no-print-directory keep make's own messages out of test-post.log,
# which check-regtest.sh reads (because its name is derived from test.log)
# as the post-test checks' error messages.
make -s --no-print-directory post-regtest-checks > test-post.log 2>&1 || true

# check-regtest.sh also writes the observed failures to test-observed.txt.
"$FJALARDIR/check-regtest.sh" --log test.log --expected "$OUTFILE" --update
