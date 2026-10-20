#!/bin/bash

# This script builds the readelf program of a Binutils release, for comparing
# its output with that of "--fjalar-debug-dump=yes".  See chapter "Updating
# Readelf from Binutils" of doc/valgrind-merge.texinfo.
#
# Usage: ./build-binutils-readelf.sh VERSION
#   VERSION is a Binutils version, such as 2.42.  First run
#   generate-binutils-patch-files.sh, which extracts that version in
#   $BINUTILS_TMP (default: ~/tmp/binutils).
#
# The script builds in $BINUTILS_TMP/build-binutils-VERSION, rather than in
# the extracted tree, which merge-binutils.sh merges from.  It prints the
# path of the readelf program.  If that program exists already, the script
# only prints its path.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

if [ $# -ne 1 ]; then
  echo "Usage: $0 VERSION" >&2
  exit 2
fi
BU=binutils-$1

BINUTILS_TMP=${BINUTILS_TMP:-$HOME/tmp/binutils}
if [ ! -f "$BINUTILS_TMP/$BU/.extracted" ]; then
  echo "$0: $BINUTILS_TMP/$BU does not exist; first run generate-binutils-patch-files.sh" >&2
  exit 1
fi
BUILDDIR=$BINUTILS_TMP/build-$BU
READELF=$BUILDDIR/binutils/readelf

if [ ! -x "$READELF" ]; then
  mkdir -p "$BUILDDIR"
  cd "$BUILDDIR"
  echo "Building $READELF; the output is in $BUILDDIR/build.log"
  if ! { "../$BU/configure" --disable-nls --disable-gdb --disable-gdbserver \
           --disable-sim --disable-gprofng \
         && make -j"$(nproc)" all-binutils; } > build.log 2>&1; then
    echo "$0: the build failed; see $BUILDDIR/build.log" >&2
    exit 1
  fi
fi
echo "$READELF"
