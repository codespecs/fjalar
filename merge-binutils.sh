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

# Keep this list in sync with generate-binutils-patch-files.sh.
BINUTILS_FILES="dwarf.c dwarf.h readelf.c elfcomm.c elfcomm.h bucomm.h demanguse.h"

# A form of the Fjalar directory that is quoted for the shell, for use in
# commands that this script prints for the user to run.
fjalar_q=$(printf %q "$FJALARDIR/valgrind/fjalar")
undo_merge="git -C $fjalar_q checkout -- $BINUTILS_FILES include libiberty &&
  find $fjalar_q -name '*.pre-merge' -delete"

# Whether this script may have changed a file.  If so, and the script fails
# for any reason, print_recovery prints how to undo the partial merge.
merge_started=false
print_recovery() {
  if [ $? -ne 0 ] && [ "$merge_started" = true ]; then
    echo "Fix the problem, undo the partial merge with" >&2
    echo "  $undo_merge" >&2
    echo "and re-run this script." >&2
  fi
}
trap print_recovery EXIT
# Run the EXIT trap on an interrupt, too.
trap "exit 130" INT TERM

# Print message $1, and how to recover from a failure, then exit.
merge_failed() {
  echo "$0: $1" >&2
  if [ "$merge_started" = false ]; then
    echo "Fix the problem, then re-run this script." >&2
  fi
  exit 1
}

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
PATCHDIR=$BUTMP/$BUOLDVER-$BUNEWVER
for f in "$PATCHDIR/include.patch" "$BUTMP/$BUOLD/.extracted" "$BUTMP/$BUNEW/.extracted"; do
  if [ ! -f "$f" ]; then
    echo "$0: $f does not exist." >&2
    echo "Run generate-binutils-patch-files.sh $BUNEWVER, then re-run this script." >&2
    exit 1
  fi
done
# Check before changing any file, so that a failure does not leave a partial
# merge.
missing=
for f in $BINUTILS_FILES; do
  for dir in "$BUTMP/$BUOLD/binutils" "$BUTMP/$BUNEW/binutils"; do
    if [ ! -f "$dir/$f" ]; then
      missing+="  $dir/$f"$'\n'
    fi
  done
done
if [ -n "$missing" ]; then
  echo "$0: these files do not exist:" >&2
  echo -n "$missing" >&2
  echo "Remove each one from BINUTILS_FILES in this script and in" >&2
  echo "generate-binutils-patch-files.sh, then re-run this script." >&2
  echo "After this script succeeds, merge each one by hand." >&2
  exit 1
fi

cd "$FJALARDIR/valgrind/fjalar"

if [ "$DRY_RUN" = false ]; then
  pre_merge=$(find . -name '*.pre-merge')
  if [ -n "$pre_merge" ]; then
    echo "$0: .pre-merge files exist, so a merge has already been done:" >&2
    echo "$pre_merge" >&2
    echo "If the merge is complete, delete them with" >&2
    echo "  find $fjalar_q -name '*.pre-merge' -delete" >&2
    echo "To start over instead, undo the merge with" >&2
    echo "  $undo_merge" >&2
    echo "and re-run this script." >&2
    exit 1
  fi
  # include.patch changes files in include/ and libiberty/.
  # shellcheck disable=SC2086 # $BINUTILS_FILES is a list of file names
  changed=$(git status --porcelain -- $BINUTILS_FILES include libiberty)
  if [ -n "$changed" ]; then
    echo "$0: these files have uncommitted changes:" >&2
    echo "$changed" >&2
    echo "Commit the changes, then re-run this script." >&2
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
patch_args=(-p1 -lu -f --no-backup-if-mismatch --merge=diff3)
if [ "$DRY_RUN" = true ]; then
  patch_args+=(--dry-run)
fi
# patch exits with status 1 if a hunk failed, including for files that
# Fjalar does not have, and with status 2 if there was trouble.
patch_status=0
if [ "$DRY_RUN" = false ]; then
  merge_started=true
fi
patch_output=$(patch "${patch_args[@]}" < "$PATCHDIR/include.patch") || patch_status=$?
awk "$SKIPFILTER" <<< "$patch_output"
if [ $patch_status -gt 1 ]; then
  merge_failed "patch failed; see its messages above."
fi

# If "git merge-file" succeeds, its exit status is the number of conflicts,
# or 127 if there are more than 127.  If it fails, its exit status is
# negative, which the shell reports as 128 or more.
for f in $BINUTILS_FILES; do
  if [ "$DRY_RUN" = true ]; then
    status=0
    git merge-file -p --diff3 "$f" "$BUTMP/$BUOLD/binutils/$f" \
      "$BUTMP/$BUNEW/binutils/$f" > /dev/null || status=$?
  else
    cp -p "$f" "$f.pre-merge"
    status=0
    git merge-file -L fjalar -L "$BUOLD" -L "$BUNEW" --diff3 \
      "$f" "$BUTMP/$BUOLD/binutils/$f" "$BUTMP/$BUNEW/binutils/$f" \
      || status=$?
  fi
  if [ $status -ge 128 ]; then
    merge_failed "git merge-file failed for $f; see its message above."
  fi
  case $status in
    1) echo "$f: 1 conflict" ;;
    127) echo "$f: 127 or more conflicts" ;;
    *) echo "$f: $status conflicts" ;;
  esac
done

if [ "$DRY_RUN" = false ]; then
  echo "Find the conflicts with:  grep -rln '^<<<<<<<' $fjalar_q"
  echo "To undo the merge:  $undo_merge"
  echo "After you resolve the conflicts, set BINUTILS_VERSION=$BUNEWVER in"
  echo "$(printf %q "$FJALARDIR/valgrind/REVISION")."
fi
