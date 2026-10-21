#!/bin/bash

# This script builds the readelf program of a Binutils release, for comparing
# its output with that of "--fjalar-debug-dump=yes".  See chapter "Updating
# Readelf from Binutils" of doc/valgrind-merge.texinfo.
#
# Usage: ./build-binutils-readelf.sh VERSION
#   VERSION is a Binutils version, such as 2.42.  First run
#   generate-binutils-patch-files.sh, which extracts that version in
#   /tmp/$USER/binutils.
#
# The script builds in /tmp/$USER/binutils/build-binutils-VERSION, rather than in
# the extracted tree, which merge-binutils.sh merges from.  It prints the
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
BU=binutils-$1

BUTMP=/tmp/$USER/binutils
# Another user could plant a Binutils tree, whose configure script
# build-binutils-readelf.sh runs, in a directory that they own or can write.
mkdir -p "$BUTMP"
for dir in "/tmp/$USER" "$BUTMP"; do
  if [ ! -O "$dir" ] || [ -n "$(find "$dir" -maxdepth 0 -perm /002)" ]; then
    echo "$0: $dir must be owned by you and not writable by others." >&2
    echo "Delete it or fix its ownership and permissions, then re-run this script." >&2
    exit 1
  fi
done
if [ ! -f "$BUTMP/$BU/.extracted" ]; then
  echo "$0: $BUTMP/$BU does not exist." >&2
  echo "Run generate-binutils-patch-files.sh NEWVER, where NEWVER is the Binutils" >&2
  echo "version being merged; it extracts both that version and the version" >&2
  echo "in valgrind/REVISION.  Then re-run this script." >&2
  echo "To build any other version, download $BU.tar.gz and its signature from" >&2
  echo "https://ftp.gnu.org/gnu/binutils/, verify the signature, extract the" >&2
  echo "tarball in $BUTMP, create file $BUTMP/$BU/.extracted, and" >&2
  echo "re-run this script." >&2
  exit 1
fi
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
