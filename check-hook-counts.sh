#!/bin/bash

# This script checks that merging a newer version of Binutils' readelf code
# into Fjalar did not lose or duplicate a call of one of Fjalar's hooks in
# dwarf.c and readelf.c.  See chapter "Updating Readelf from Binutils" of
# doc/valgrind-merge.texinfo.
#
# Usage: ./check-hook-counts.sh [BASE]
#   BASE is the commit whose dwarf.c and readelf.c to compare with.  The
#   default is the commit where the current branch started from the master
#   branch of https://github.com/codespecs/fjalar, even if the branch already
#   has commits, such as earlier steps of a merge.
#
# The hooks are the functions declared in typedata.h, fjalar_dwarf.h, and
# fjalar_include.h, which build Fjalar's DWARF entries and symbol tables.
# For each of dwarf.c and readelf.c, the script counts the occurrences of
# each hook in BASE's version and in the work tree's version, and prints
#   FILE HOOK OLDCOUNT NEWCOUNT
# for each hook whose count changed.  Explain each difference.
#
# The counts omit "#if 0" regions and comments, so that they notice a hook
# that conflict resolution moved into disabled code.  They do include string
# literals, so a hook's name in a debugging message counts as a call; check
# any difference that involves one.
#
# Exit status: 0 if no count changed, 1 if some count changed, 2 on error.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

if [ $# -gt 1 ]; then
  echo "Usage: $0 [BASE]" >&2
  exit 2
fi

FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"
cd "$FJALARDIR"

if [ $# -eq 1 ]; then
  base=$1
else
  if ! git fetch -q https://github.com/codespecs/fjalar.git master; then
    echo "$0: cannot fetch the master branch of codespecs/fjalar" >&2
    exit 2
  fi
  base=$(git merge-base FETCH_HEAD HEAD)
fi

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

# Print C file $1 without its comments and "#if 0" regions.  Comments are
# removed first, so that a directive in a comment does not end or start a
# region.
live() {
  gcc -fpreprocessed -dD -E -P -x c - < "$1" 2> /dev/null \
    | awk '!skip && /^[ \t]*#[ \t]*if[ \t]+0([^0-9]|$)/ {skip=1; depth=1; next}
           skip && /^[ \t]*#[ \t]*if/ {depth++; next}
           skip && /^[ \t]*#[ \t]*endif/ {if (--depth == 0) skip=0; next}
           skip && depth == 1 && /^[ \t]*#[ \t]*(else|elif)/ {skip=0; next}
           !skip'
}

decl='^[A-Za-z_][A-Za-z0-9_ *]*[ *]([A-Za-z_][A-Za-z0-9_]*)\(.*'
hooks=$(sed -nE "s/$decl/\1/p" \
          valgrind/fjalar/{typedata,fjalar_dwarf,fjalar_include}.h \
          | sort -u)
if [ -z "$hooks" ]; then
  echo "$0: found no hook declarations" >&2
  exit 2
fi

for file in dwarf.c readelf.c; do
  if ! git show "$base:valgrind/fjalar/$file" > "$tmpdir/$file.old"; then
    echo "$0: cannot read valgrind/fjalar/$file at $base" >&2
    exit 2
  fi
  # Without these checks, a failure of gcc would make every count 0.
  if ! live "$tmpdir/$file.old" > "$tmpdir/$file.old.live"; then
    echo "$0: cannot process valgrind/fjalar/$file at $base" >&2
    exit 2
  fi
  if ! live valgrind/fjalar/$file > "$tmpdir/$file.new.live"; then
    echo "$0: cannot process valgrind/fjalar/$file" >&2
    exit 2
  fi
done

echo "$hooks" > "$tmpdir/hooks"
# For each file, count the words that are hooks in both versions at once.
# shellcheck disable=SC2016 # The $0 is awk's, not the shell's.
changed=$(for file in dwarf.c readelf.c; do
  awk -v file="$file" \
    'FILENAME == ARGV[1] {hook[$0]; next}
     {n = split($0, words, /[^A-Za-z0-9_]+/)
      for (i = 1; i <= n; i++)
        if (words[i] in hook) count[FILENAME, words[i]]++}
     END {for (h in hook)
            if (count[ARGV[2], h] != count[ARGV[3], h])
              print file, h, count[ARGV[2], h] + 0, count[ARGV[3], h] + 0}' \
    "$tmpdir/hooks" "$tmpdir/$file.old.live" "$tmpdir/$file.new.live" | sort
done)

if [ -n "$changed" ]; then
  echo "$changed"
  exit 1
fi
echo "No hook count changed since $base."
