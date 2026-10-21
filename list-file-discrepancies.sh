#!/bin/bash

# This script lists the disagreements between the Fjalar tree that contains
# this script and an upstream Valgrind tree.  Use it while merging a newer
# version of upstream Valgrind into Fjalar; see doc/valgrind-merge.texinfo.
# Usage: list-file-discrepancies.sh [VALGRIND-DIR]
# VALGRIND-DIR is a git clone of upstream Valgrind; the default is
# $INV/valgrind-old.  The script prints four lists, each preceded by a
# heading line that starts with "#":
#  * files that Fjalar tracks but VALGRIND-DIR does not have,
#  * Memcheck files that valgrind/fjalar has but VALGRIND-DIR does not have,
#  * Memcheck files that VALGRIND-DIR has but valgrind/fjalar lacks, and
#  * files that VALGRIND-DIR has but Fjalar does not track.
# Each file name is relative to the top of the Fjalar tree, except in the
# last list, where it is relative to VALGRIND-DIR.  So each list, without its
# heading, can be given to the commands in doc/valgrind-merge.texinfo that
# remove or add the files.

set -e
set -o pipefail

if [ $# -gt 1 ]; then
  echo "Usage: $0 [VALGRIND-DIR]" >&2
  exit 1
fi
if [ $# -eq 1 ]; then
  valgrind=$1
elif [ -n "$INV" ]; then
  valgrind=$INV/valgrind-old
else
  echo "$0: INV is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi
# Make "cd" with a relative directory resolve it against the current
# directory.
unset CDPATH
# A subdirectory of a clone would make "git ls-files" print paths relative
# to that subdirectory.
toplevel=$(git -C "$valgrind" rev-parse --show-toplevel 2> /dev/null) || toplevel=
if [ -z "$toplevel" ] || [ "$toplevel" != "$(cd -- "$valgrind" 2> /dev/null && pwd -P)" ]; then
  echo "$0: $valgrind is not the top level of a git clone." >&2
  exit 1
fi

fjalar=$(dirname -- "$(readlink -f -- "$0")")

# Make sort and comm agree on the sort order; in other locales, comm can
# list files that both trees have.
export LC_ALL=C

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

# Without --deduplicate, "git ls-files" prints an unmerged file once per stage.
git -C "$fjalar" ls-files --deduplicate valgrind | sed 's|^valgrind/||' | sort > "$tmpdir/fjalar-files"
sed -n 's|^fjalar/||p' "$tmpdir/fjalar-files" \
  | { grep -E '^(mc_|memcheck)' || true; } > "$tmpdir/fjalar-memcheck-files"
git -C "$valgrind" ls-files | sort > "$tmpdir/valgrind-files"
sed -n 's|^memcheck/||p' "$tmpdir/valgrind-files" > "$tmpdir/valgrind-memcheck-files"

echo "# Files that Fjalar tracks but $valgrind does not have:"
comm -23 <(grep -v -e '^fjalar/' -e '^REVISION$' "$tmpdir/fjalar-files" || true) \
         "$tmpdir/valgrind-files" \
  | sed 's|^|valgrind/|'

echo "# Memcheck files that valgrind/fjalar has but $valgrind does not have:"
comm -23 "$tmpdir/fjalar-memcheck-files" "$tmpdir/valgrind-memcheck-files" \
  | sed 's|^|valgrind/fjalar/|'

echo "# Memcheck files that $valgrind has but valgrind/fjalar lacks:"
comm -13 "$tmpdir/fjalar-memcheck-files" \
         <(grep -E '^(mc_|memcheck)' "$tmpdir/valgrind-memcheck-files" || true) \
  | sed 's|^|valgrind/fjalar/|'

echo "# Files that $valgrind has but Fjalar does not track:"
comm -13 "$tmpdir/fjalar-files" "$tmpdir/valgrind-files"
