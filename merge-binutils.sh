#!/bin/bash

# This script merges a newer version of Binutils' readelf code into Fjalar.
# See chapter "Updating Readelf from Binutils" of doc/valgrind-merge.texinfo.
# First run generate-binutils-patch-files.sh with the same NEWVER.
#
# Usage: ./merge-binutils.sh [--dry-run] NEWVER
#   NEWVER is the Binutils version to merge, such as 2.42.  The old version
#   is BINUTILS_VERSION in valgrind/REVISION.
#   --dry-run  Change no file.  Print what applying include.patch would
#              print, and the number of conflicts that merging each of
#              Fjalar's copies of files from Binutils' binutils/ directory
#              would have.
#
# Without --dry-run, the script applies include.patch, and merges each of
# Fjalar's copies of files from Binutils' binutils/ directory with
# "git merge-file".  Both write conflicts inline as
# <<<<<<< / ||||||| / ======= / >>>>>>> markers, rather than creating .rej
# files.  The script first copies each merged file to FILE.pre-merge, for use
# with a visual merge tool.  It refuses to run if any of those files has
# uncommitted changes or a .pre-merge copy, because it would then merge the
# same changes twice.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

# Make "cd" with a relative directory resolve it against the current
# directory, as "git -C" does.
unset CDPATH

DRY_RUN=false
if [ "${1-}" = --dry-run ]; then
  DRY_RUN=true
  shift
fi
if [ $# -ne 1 ]; then
  echo "Usage: $0 [--dry-run] NEWVER" >&2
  exit 2
fi
BUNEWVER=$1

FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"
BUOLDVER=$(sed -n 's/^export BINUTILS_VERSION=//p' "$FJALARDIR/valgrind/REVISION")
if [ -z "$BUOLDVER" ]; then
  echo "$0: no BINUTILS_VERSION in $FJALARDIR/valgrind/REVISION" >&2
  exit 1
fi
BUOLD=binutils-$BUOLDVER
BUNEW=binutils-$BUNEWVER

# Keep this list in sync with generate-binutils-patch-files.sh.
BINUTILS_FILES="dwarf.c dwarf.h readelf.c elfcomm.c elfcomm.h bucomm.h demanguse.h"

BINUTILS_TMP=${BINUTILS_TMP:-$HOME/tmp/binutils}
# Make the directory absolute, because the script changes directory.
BINUTILS_TMP=$(realpath -m "$BINUTILS_TMP")
PATCHDIR=$BINUTILS_TMP/$BUOLDVER-$BUNEWVER
for f in "$PATCHDIR/include.patch" "$BINUTILS_TMP/$BUOLD/.extracted" "$BINUTILS_TMP/$BUNEW/.extracted"; do
  if [ ! -f "$f" ]; then
    echo "$0: $f does not exist; first run generate-binutils-patch-files.sh $BUNEWVER" >&2
    exit 1
  fi
done
# Check before changing any file, so that a failure does not leave a partial
# merge.
missing=
for f in $BINUTILS_FILES; do
  for dir in "$BINUTILS_TMP/$BUOLD/binutils" "$BINUTILS_TMP/$BUNEW/binutils"; do
    if [ ! -f "$dir/$f" ]; then
      missing+="  $dir/$f"$'\n'
    fi
  done
done
if [ -n "$missing" ]; then
  echo "$0: these files do not exist; merge them by hand, and update BINUTILS_FILES:" >&2
  echo -n "$missing" >&2
  exit 1
fi

cd "$FJALARDIR/valgrind/fjalar"

if [ "$DRY_RUN" = false ]; then
  pre_merge=$(find . -name '*.pre-merge')
  if [ -n "$pre_merge" ]; then
    echo "$0: .pre-merge files exist, so a merge has already been done:" >&2
    echo "$pre_merge" >&2
    echo "$0: Delete them once the merge is complete, or undo the merge." >&2
    exit 1
  fi
  # include.patch changes files in include/ and libiberty/.
  # shellcheck disable=SC2086 # $BINUTILS_FILES is a list of file names
  changed=$(git status --porcelain -- $BINUTILS_FILES include libiberty)
  if [ -n "$changed" ]; then
    echo "$0: these files have uncommitted changes; commit them first:" >&2
    echo "$changed" >&2
    exit 1
  fi
fi

# Patch messages about Binutils files that Fjalar does not have, which
# include.patch also changes, are not of interest.  This filter removes them.
# It also prints a "patching file" line only if a message about that file
# follows it.
# shellcheck disable=SC2016 # The $0 is awk's, not the shell's.
SKIPFILTER='/can.t find file to patch/ {skip=1}
  /^(checking|patching) file / {file=$0; next}
  !skip && !/hunks? ignored/ {if (file != "") print file; file=""; print}
  /Skipping patch\./ {skip=0; file=""}'
patch_args=(-p1 -lu -f --no-backup-if-mismatch)
if [ "$DRY_RUN" = true ]; then
  patch_args+=(--dry-run)
else
  patch_args+=(--merge=diff3)
fi
# patch exits with status 1 if a hunk failed, including for files that
# Fjalar does not have, and with status 2 if there was trouble.
patch_status=0
patch_output=$(patch "${patch_args[@]}" < "$PATCHDIR/include.patch") || patch_status=$?
awk "$SKIPFILTER" <<< "$patch_output"
if [ $patch_status -gt 1 ]; then
  echo "$0: patch failed" >&2
  exit 1
fi

# "git merge-file" exits with the number of conflicts, truncated to 127, and
# with a negative status, which the shell reports as 128 or more, on error.
for f in $BINUTILS_FILES; do
  if [ "$DRY_RUN" = true ]; then
    status=0
    git merge-file -p --diff3 "$f" "$BINUTILS_TMP/$BUOLD/binutils/$f" \
      "$BINUTILS_TMP/$BUNEW/binutils/$f" > /dev/null || status=$?
  else
    cp -p "$f" "$f.pre-merge"
    status=0
    git merge-file -L fjalar -L "$BUOLD" -L "$BUNEW" --diff3 \
      "$f" "$BINUTILS_TMP/$BUOLD/binutils/$f" "$BINUTILS_TMP/$BUNEW/binutils/$f" \
      || status=$?
  fi
  if [ $status -ge 128 ]; then
    echo "$0: git merge-file failed for $f" >&2
    exit 1
  fi
  case $status in
    1) echo "$f: 1 conflict" ;;
    127) echo "$f: 127 or more conflicts" ;;
    *) echo "$f: $status conflicts" ;;
  esac
done

if [ "$DRY_RUN" = false ]; then
  echo "Find the conflicts with:  grep -rln '^<<<<<<<' $FJALARDIR/valgrind/fjalar"
  echo "To undo the merge:  git -C $FJALARDIR/valgrind/fjalar checkout -- $BINUTILS_FILES include libiberty &&"
  echo "  find $FJALARDIR/valgrind/fjalar -name '*.pre-merge' -delete"
fi
