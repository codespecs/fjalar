#!/bin/bash

# This script builds the readelf program of a Binutils release, for comparing
# its output with that of "--fjalar-debug-dump=yes".  See chapter "Updating
# Readelf from Binutils" of doc/valgrind-merge.texinfo.
#
# Usage: ./build-binutils-readelf.sh VERSION
#   VERSION is a Binutils version, such as 2.42.
#
# The script downloads and extracts the whole of VERSION with
# download-binutils.sh, unless that has been done already.  It builds in
# /tmp/$USER/binutils/build-binutils-VERSION, rather than in the extracted
# tree, which merge-binutils.sh merges from.  It prints the
# path of the readelf program on standard output, and its progress messages
# on standard error.  If that program exists already, the script only prints
# its path.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

# Make "cd" with a relative directory resolve it against the current
# directory, as "git -C" does.
unset CDPATH

if [ $# -ne 1 ]; then
  echo "Usage: $0 VERSION" >&2
  exit 2
fi
if ! [[ "$1" =~ ^[0-9]+(\.[0-9]+)+$ ]]; then
  echo "$0: VERSION must be a version number such as 2.42, not $1" >&2
  exit 2
fi
BU=binutils-$1

FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"
"$FJALARDIR/download-binutils.sh" --full "$1"
BUTMP=/tmp/$USER/binutils
BUILDDIR=$BUTMP/build-$BU
READELF=$BUILDDIR/binutils/readelf

if [ ! -x "$READELF" ]; then
  mkdir -p "$BUILDDIR"
  cd "$BUILDDIR"
  echo "Building $READELF; the output is in $BUILDDIR/build.log" >&2
  if ! { "../$BU/configure" --disable-nls --disable-gdb --disable-gdbserver \
           --disable-sim --disable-gprofng \
         && make -j"$(nproc)" all-binutils; } > build.log 2>&1; then
    echo "$0: the build failed; see $BUILDDIR/build.log" >&2
    echo "Fix the problem, then re-run this script." >&2
    exit 1
  fi
fi
echo "$READELF"
