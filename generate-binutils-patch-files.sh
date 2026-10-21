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
# The script works in /tmp/$USER/binutils.  It downloads binutils-OLDVER.tar.gz
# and binutils-NEWVER.tar.gz, unless they have been downloaded already,
# verifies their signatures, and extracts them.  It writes these files to
# /tmp/$USER/binutils/OLDVER-NEWVER/:
#   include.patch      the upstream changes to the files in include/ and to
#                      libiberty/dwarfnames.c, which merge-binutils.sh
#                      applies
#   *-binutils-vs-fjalar.diff
#                      Fjalar's changes to each Binutils-derived file, a
#                      checklist for verifying that the merge kept them
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
  echo "Add a line \"export BINUTILS_VERSION=OLDVER\" to that file, where OLDVER" >&2
  echo "is the Binutils version of Fjalar's readelf code, then re-run this script." >&2
  exit 1
fi
if [ "$BUOLDVER" = "$BUNEWVER" ]; then
  echo "$0: Fjalar's readelf code is already from Binutils $BUNEWVER" >&2
  echo "There is nothing to merge.  To merge a newer version, pass it as NEWVER." >&2
  exit 1
fi
BUOLD=binutils-$BUOLDVER
BUNEW=binutils-$BUNEWVER

# Keep this list in sync with merge-binutils.sh.
BINUTILS_FILES="dwarf.c dwarf.h readelf.c elfcomm.c elfcomm.h bucomm.h demanguse.h"

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
OUTDIR=$BUTMP/$BUOLDVER-$BUNEWVER
mkdir -p "$OUTDIR"
cd "$BUTMP"

# Usage: download URL
# Downloads URL into the current directory, unless the file exists already.
# It downloads to a temporary name, so that an interrupted download leaves no
# partial file that a later run would reuse.
download() {
  local file
  file=$(basename "$1")
  if [ ! -f "$file" ]; then
    wget -nv -O "$file.part" "$1"
    mv "$file.part" "$file"
  fi
}

# gpgv checks the signatures against the GNU keyring, rather than against the
# user's own keyring, which may lack the signers' keys.
download https://ftp.gnu.org/gnu/gnu-keyring.gpg
for f in $BUOLD $BUNEW; do
  download https://ftp.gnu.org/gnu/binutils/"$f.tar.gz"
  download https://ftp.gnu.org/gnu/binutils/"$f.tar.gz.sig"
  if ! gpgv --keyring "$BUTMP/gnu-keyring.gpg" "$f.tar.gz.sig" "$f.tar.gz"; then
    echo "$0: the signature of $BUTMP/$f.tar.gz is not valid" >&2
    echo "The download may be corrupt, or the keyring may lack a newer signer's key." >&2
    echo "Delete $BUTMP/$f.tar.gz, $BUTMP/$f.tar.gz.sig, and" >&2
    echo "$BUTMP/gnu-keyring.gpg, so that they are downloaded again, then re-run" >&2
    echo "this script.  If the signature is still not valid, do not use the file." >&2
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
    echo "$0: diff $* failed; see its message above" >&2
    echo "Fix the problem, then re-run this script." >&2
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
  run_diff -ub "$BUTMP/$BUOLD/binutils/$f" "$f" > "$OUTDIR/$f-binutils-vs-fjalar.diff"
done
for f in $(cd include && find . -type f | sed 's|^\./||' | sort); do
  if [ -f "$BUTMP/$BUOLD/include/$f" ]; then
    run_diff -ub "$BUTMP/$BUOLD/include/$f" "include/$f"
  else
    echo "Only in Fjalar: include/$f"
  fi
done > "$OUTDIR/include-binutils-vs-fjalar.diff"
run_diff -ub "$BUTMP/$BUOLD/libiberty/dwarfnames.c" libiberty/dwarfnames.c \
  > "$OUTDIR/dwarfnames-binutils-vs-fjalar.diff"

echo "Wrote the patch and diff files for $BUOLDVER -> $BUNEWVER in $OUTDIR"
