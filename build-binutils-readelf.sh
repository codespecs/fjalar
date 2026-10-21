#!/bin/bash

# This script builds the readelf program of a Binutils release, for comparing
# its output with that of "--fjalar-debug-dump=yes".  See chapter "Updating
# Readelf from Binutils" of doc/valgrind-merge.texinfo.
#
# Usage: ./build-binutils-readelf.sh VERSION
#   VERSION is a Binutils version, such as 2.42.
#
# The script prints the path of the readelf program on standard output.  If
# that program exists already, the script only prints its path.  Otherwise,
# it downloads and extracts the whole of VERSION with download-binutils.sh,
# unless that has been done already, and builds it in
# /tmp/$USER/binutils/build-binutils-VERSION, rather than in the extracted
# tree, which merge-binutils.sh merges from.  It prints its progress messages
# on standard error.

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
# The Fjalar tree that contains this script, even if $0 is a symbolic link.
FJALARDIR=$(dirname -- "$(readlink -f -- "$0")")
source "$FJALARDIR/binutils-common.sh"
check_version VERSION "$1"
BU=binutils-$1

BUILDDIR=$BUTMP/build-$BU
READELF=$BUILDDIR/binutils/readelf

# The check keeps the script from printing the path of a program that another
# user planted.
make_butmp
if [ ! -x "$READELF" ]; then
  "$FJALARDIR/download-binutils.sh" --full "$1"
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
