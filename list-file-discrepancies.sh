#!/bin/bash

# This script lists the disagreements between the Fjalar tree that contains
# this script and an upstream Valgrind tree.  Use it while merging a newer
# version of upstream Valgrind into Fjalar; see doc/valgrind-merge.texinfo.
# Usage: list-file-discrepancies.sh [VALGRIND-DIR]
# VALGRIND-DIR is a git clone of upstream Valgrind; the default is
# $INV/valgrind-old.  The script prints five lists, each preceded by a
# heading line that starts with "#":
#  * files that Fjalar tracks but VALGRIND-DIR does not have,
#  * Memcheck files that valgrind/fjalar has but VALGRIND-DIR does not have,
#    where a Memcheck file in valgrind/fjalar is one whose name starts with
#    "mc_" or "memcheck", because the other files there are Fjalar's own,
#  * Memcheck files that VALGRIND-DIR has but valgrind/fjalar lacks, where
#    the Memcheck files of VALGRIND-DIR are those that merge-valgrind.sh
#    merges into valgrind/fjalar:  all of memcheck/ except docs/, tests/,
#    and Makefile.am,
#  * files that VALGRIND-DIR has but Fjalar does not track, and
#  * files whose mode in Fjalar differs from their mode in VALGRIND-DIR, such
#    as a script that lacks its execute bit, each preceded by its mode in
#    VALGRIND-DIR and a space.
# Each file name is relative to the top of the Fjalar tree, except in the
# fourth list, where it is relative to VALGRIND-DIR.  So each list, without
# its heading, can be given to the commands in doc/valgrind-merge.texinfo
# that remove or add the files or change their modes.

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
# The files that merge-valgrind.sh merges into valgrind/fjalar.
sed -n 's|^memcheck/||p' "$tmpdir/valgrind-files" \
  | { grep -v -e '^docs/' -e '^tests/' -e '^Makefile\.am$' || true; } \
  > "$tmpdir/valgrind-memcheck-files"

echo "# Files that Fjalar tracks but $valgrind does not have:"
comm -23 <(grep -v -e '^fjalar/' -e '^REVISION$' "$tmpdir/fjalar-files" || true) \
         "$tmpdir/valgrind-files" \
  | sed 's|^|valgrind/|'

echo "# Memcheck files that valgrind/fjalar has but $valgrind does not have:"
comm -23 "$tmpdir/fjalar-memcheck-files" "$tmpdir/valgrind-memcheck-files" \
  | sed 's|^|valgrind/fjalar/|'

echo "# Memcheck files that $valgrind has but valgrind/fjalar lacks:"
comm -13 <(sed -n 's|^fjalar/||p' "$tmpdir/fjalar-files") \
         "$tmpdir/valgrind-memcheck-files" \
  | sed 's|^|valgrind/fjalar/|'

echo "# Files that $valgrind has but Fjalar does not track:"
comm -13 "$tmpdir/fjalar-files" "$tmpdir/valgrind-files"

# The 3-way merge treats a mode that differs from the base Valgrind's as
# Fjalar's change, and keeps it.  Each line of "git ls-files --stage" is a
# mode, an object name, a stage number, a tab, and a path.  An unmerged file
# has no stage 0, so its stage 2, Fjalar's version, is used.  Each Memcheck
# file in valgrind/fjalar that merge-valgrind.sh merges is compared with
# the one in memcheck/.
echo "# Files whose mode differs from that in $valgrind, with the mode in $valgrind:"
# shellcheck disable=SC2016 # The $s are awk's, not the shell's.
awk -F '\t' 'FILENAME == ARGV[1] { merged["memcheck/" $0]; next }
  FILENAME == ARGV[2] { split($1, f, " "); mode[$2] = f[1]; next }
  { split($1, f, " ")
    if (f[3] != 0 && f[3] != 2) next
    key = substr($2, length("valgrind/") + 1)
    if (key == "REVISION") next
    if (key ~ /^fjalar\//) {
      key = "memcheck/" substr(key, length("fjalar/") + 1)
      if (!(key in merged)) next
    }
    if ((key in mode) && mode[key] != f[1]) print mode[key] " " $2 }' \
  "$tmpdir/valgrind-memcheck-files" \
  <(git -C "$valgrind" ls-files --stage) \
  <(git -C "$fjalar" ls-files --stage -- valgrind)
