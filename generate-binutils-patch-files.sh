#!/bin/bash

# This script creates the patch and diff files that are used when merging a
# newer version of Binutils' readelf code into Fjalar.  See chapter
# "Updating Readelf from Binutils" of doc/valgrind-merge.texinfo.
#
# Usage: ./generate-binutils-patch-files.sh NEWVER
#   NEWVER is the Binutils version to merge, such as 2.42.  The old version
#   is BINUTILS_VERSION in valgrind/REVISION, which is the version that
#   Fjalar's copy of the readelf code is from.
#
# The script works in $BINUTILS_TMP (default: ~/tmp/binutils).  It downloads
# binutils-OLDVER.tar.gz and binutils-NEWVER.tar.gz, unless they have been
# downloaded already, verifies their signatures, and extracts them.  It
# writes these files to $BINUTILS_TMP/OLDVER-NEWVER/:
#   include.patch      the upstream changes to the files in include/ and to
#                      libiberty/dwarfnames.c, which merge-binutils.sh
#                      applies
#   *-binutils-vs-fjalar.diff
#                      Fjalar's changes to each Binutils-derived file,
#                      for reference while resolving conflicts
# There is no patch file for Binutils' binutils/ directory:
# merge-binutils.sh merges each of Fjalar's copies of files from that
# directory with "git merge-file".

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

# Make "cd" with a relative directory resolve it against the current
# directory, as "git -C" does.
unset CDPATH

if [ $# -ne 1 ]; then
  echo "Usage: $0 NEWVER" >&2
  exit 2
fi
BUNEWVER=$1
if ! [[ "$BUNEWVER" =~ ^[0-9]+(\.[0-9]+)+$ ]]; then
  echo "$0: NEWVER must be a version number such as 2.42, not $BUNEWVER" >&2
  exit 2
fi

FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"
BUOLDVER=$(sed -n 's/^export BINUTILS_VERSION=//p' "$FJALARDIR/valgrind/REVISION")
if [ -z "$BUOLDVER" ]; then
  echo "$0: no BINUTILS_VERSION in $FJALARDIR/valgrind/REVISION" >&2
  exit 1
fi
if [ "$BUOLDVER" = "$BUNEWVER" ]; then
  echo "$0: Fjalar's readelf code is already from Binutils $BUNEWVER" >&2
  exit 1
fi
BUOLD=binutils-$BUOLDVER
BUNEW=binutils-$BUNEWVER

# Keep this list in sync with merge-binutils.sh.
BINUTILS_FILES="dwarf.c dwarf.h readelf.c elfcomm.c elfcomm.h bucomm.h demanguse.h"

BINUTILS_TMP=${BINUTILS_TMP:-$HOME/tmp/binutils}
# Make the directory absolute, because the script changes directory.
BINUTILS_TMP=$(realpath -m "$BINUTILS_TMP")
OUTDIR=$BINUTILS_TMP/$BUOLDVER-$BUNEWVER
mkdir -p "$OUTDIR"
cd "$BINUTILS_TMP"

# gpgv checks the signatures against the GNU keyring, rather than against the
# user's own keyring, which may lack the signers' keys.
if [ ! -f gnu-keyring.gpg ]; then
  wget -nv https://ftp.gnu.org/gnu/gnu-keyring.gpg
fi
for f in $BUOLD $BUNEW; do
  if [ ! -f "$f.tar.gz" ] || [ ! -f "$f.tar.gz.sig" ]; then
    wget -nv https://ftp.gnu.org/gnu/binutils/"$f.tar.gz" \
      https://ftp.gnu.org/gnu/binutils/"$f.tar.gz.sig"
  fi
  if ! gpgv --keyring "$BINUTILS_TMP/gnu-keyring.gpg" "$f.tar.gz.sig" "$f.tar.gz"; then
    echo "$0: the signature of $BINUTILS_TMP/$f.tar.gz is not valid" >&2
    exit 1
  fi
  # A tree that an earlier run extracted only partly is not reused.
  if [ ! -f "$f/.extracted" ]; then
    rm -rf "$f"
    tar xzf "$f.tar.gz"
    touch "$f/.extracted"
  fi
done

# Usage: run_diff DIFF-ARGS...
# Runs diff.  diff exits with status 1 if the files differ, which is
# expected, and with status 2 if there was trouble.
run_diff() {
  local status=0
  diff "$@" || status=$?
  if [ $status -gt 1 ]; then
    echo "$0: diff $* failed" >&2
    exit 1
  fi
}

# "diff -ur" without -N lists a new upstream header only as "Only in ...";
# Fjalar copies the ones that it needs by hand.
{
  run_diff -ur "$BUOLD/include" "$BUNEW/include"
  run_diff -u "$BUOLD/libiberty/dwarfnames.c" "$BUNEW/libiberty/dwarfnames.c"
} > "$OUTDIR/include.patch"

cd "$FJALARDIR/valgrind/fjalar"
for f in $BINUTILS_FILES; do
  run_diff -ub "$BINUTILS_TMP/$BUOLD/binutils/$f" "$f" > "$OUTDIR/$f-binutils-vs-fjalar.diff"
done
for f in $(cd include && find . -type f | sed 's|^\./||' | sort); do
  if [ -f "$BINUTILS_TMP/$BUOLD/include/$f" ]; then
    run_diff -ub "$BINUTILS_TMP/$BUOLD/include/$f" "include/$f"
  else
    echo "Only in Fjalar: include/$f"
  fi
done > "$OUTDIR/include-binutils-vs-fjalar.diff"
run_diff -ub "$BINUTILS_TMP/$BUOLD/libiberty/dwarfnames.c" libiberty/dwarfnames.c \
  > "$OUTDIR/dwarfnames-binutils-vs-fjalar.diff"

echo "Wrote the patch and diff files for $BUOLDVER -> $BUNEWVER in $OUTDIR"
