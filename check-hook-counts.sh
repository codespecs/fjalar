#!/bin/bash

# This script checks that merging a newer version of Binutils' readelf code
# into Fjalar did not lose or duplicate a call of one of Fjalar's hooks in
# dwarf.c and readelf.c.  See chapter "Updating Readelf from Binutils" of
# doc/valgrind-merge.texinfo.
#
# Usage: ./check-hook-counts.sh [BASE_COMMIT]
#   BASE_COMMIT is the commit whose dwarf.c and readelf.c to compare with.
#   The default is the commit where the current branch started from the
#   master branch of https://github.com/codespecs/fjalar, even if the branch
#   already has commits, such as earlier steps of a merge.
#
# The hooks are the functions declared in typedata.h, fjalar_dwarf.h,
# fjalar_include.h, fjalar_main.h, and GenericHashtable.h, which build
# Fjalar's DWARF entries, symbol tables, and line-number table.
# A call of a hook is an ordinary C function call that Fjalar added to the
# Binutils code, such as
#   if (entry && tag_is_formal_parameter(entry->tag_name)) {
#     harvest_formal_param_location_atom(entry, op, uvalue);
# which contains calls of the hooks tag_is_formal_parameter and
# harvest_formal_param_location_atom.  The script does not parse calls; it
# counts every occurrence of a hook's name as a whole word.
# For each of dwarf.c and readelf.c, the script counts the occurrences of
# each hook in BASE_COMMIT's version and in the work tree's version, and prints
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
  echo "Usage: $0 [BASE_COMMIT]" >&2
  exit 2
fi

FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"
cd "$FJALARDIR"

if [ $# -eq 1 ]; then
  base_commit=$1
else
  if ! git fetch -q https://github.com/codespecs/fjalar.git master; then
    echo "$0: cannot fetch the master branch of codespecs/fjalar" >&2
    exit 2
  fi
  base_commit=$(git merge-base FETCH_HEAD HEAD)
fi

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

# Print C file $1 without its comments and "#if 0" regions.  Comments are
# removed first, so that a directive in a comment does not end or start a
# region.  Only a condition that is exactly "0" is known to be false:  a
# region ends at its "#else" or at an "#elif" whose condition is not "0",
# and the code after that is kept even if it might be disabled.
without_comments() {
  gcc -fpreprocessed -dD -E -P -x c - < "$1" 2> /dev/null \
    | awk '!skip && /^[ \t]*#[ \t]*if[ \t]+0[ \t]*$/ {skip=1; depth=1; next}
           skip && /^[ \t]*#[ \t]*if/ {depth++; next}
           skip && /^[ \t]*#[ \t]*endif/ {if (--depth == 0) skip=0; next}
           skip && depth == 1 && /^[ \t]*#[ \t]*elif[ \t]+0[ \t]*$/ {next}
           skip && depth == 1 && /^[ \t]*#[ \t]*(else|elif)/ {skip=0; next}
           !skip'
}

# A regex for the first line of a C function declaration that starts in
# column 0:  a return type of identifiers, spaces, and "*", then the function
# name (group 1), then "(".  It does not match a declaration whose return type
# is on the previous line.
decl='^[A-Za-z_][A-Za-z0-9_ *]*[ *]([A-Za-z_][A-Za-z0-9_]*)\(.*'
hooks=$(sed -nE "s/$decl/\1/p" \
          valgrind/fjalar/{typedata,fjalar_dwarf,fjalar_include,fjalar_main,GenericHashtable}.h \
          | sort -u)
if [ -z "$hooks" ]; then
  echo "$0: found no hook declarations" >&2
  exit 2
fi

for file in dwarf.c readelf.c; do
  if ! git show "$base_commit:valgrind/fjalar/$file" > "$tmpdir/$file.old"; then
    echo "$0: cannot read valgrind/fjalar/$file at $base_commit" >&2
    exit 2
  fi
  # Without these checks, a failure of gcc would make every count 0.
  if ! without_comments "$tmpdir/$file.old" > "$tmpdir/$file.old.live"; then
    echo "$0: cannot process valgrind/fjalar/$file at $base_commit" >&2
    exit 2
  fi
  if ! without_comments valgrind/fjalar/$file > "$tmpdir/$file.new.live"; then
    echo "$0: cannot process valgrind/fjalar/$file" >&2
    exit 2
  fi
done

echo "$hooks" > "$tmpdir/hooks"
changed=$(for file in dwarf.c readelf.c; do
  python3 compare-hook-counts.py "$tmpdir/hooks" \
    "$tmpdir/$file.old.live" "$tmpdir/$file.new.live" "$file" || exit 2
done)

if [ -n "$changed" ]; then
  echo "$changed"
  echo "For each line above, find out why the count of HOOK in FILE changed from" >&2
  echo "OLDCOUNT to NEWCOUNT.  If the merge lost or duplicated a call by mistake," >&2
  echo "fix it, then re-run this script.  Each run reports every difference, even" >&2
  echo "one that you have already explained.  The check is complete when you can" >&2
  echo "explain every difference that remains." >&2
  exit 1
fi
echo "No hook count changed since $base_commit."
