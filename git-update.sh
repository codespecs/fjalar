#!/bin/bash

# This script prints the git commands that add to Fjalar the files that the
# Valgrind developers added between $INV/valgrind-old and $INV/valgrind-new,
# and that remove the files that they removed.  Run the commands from the
# top of the Fjalar tree, after applying coregrind.patch and memcheck.patch
# (see doc/valgrind-merge.texinfo).
# Usage: git-update.sh > git.script

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

if [ -z "$INV" ]; then
  echo "$0: INV is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi

for dir in "$INV/valgrind-old" "$INV/valgrind-new"; do
  if [ ! -d "$dir" ]; then
    echo "$0: $dir does not exist." >&2
    exit 1
  fi
done

# The Fjalar tree that contains this script.
fjalar=$(dirname "$(readlink -f "$0")")

# Make sort and comm agree on the sort order.
export LC_ALL=C

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

# Paths are NUL-terminated throughout, so any file name works.
git -C "$INV/valgrind-old" ls-files -z | sort -z > "$tmpdir/old"
git -C "$INV/valgrind-new" ls-files -z | sort -z > "$tmpdir/new"
comm -z -13 "$tmpdir/old" "$tmpdir/new" > "$tmpdir/added"
comm -z -23 "$tmpdir/old" "$tmpdir/new" > "$tmpdir/removed"

# Usage: memcheck_files < PATHS
# Prints the paths under memcheck/ that memcheck.patch covers, without the
# memcheck/ prefix.  The excluded files are the ones that
# generate-patch-files.sh excludes from memcheck.patch.
memcheck_files() {
  { grep -z '^memcheck/' || [ $? -eq 1 ]; } \
    | sed -z 's|^memcheck/||' \
    | { grep -z -v -E '(^|/)(docs|tests)/|(^|/)Makefile\.am$' || [ $? -eq 1 ]; }
}

# Usage: print_commands COMMAND DIR < PATHS
# Prints the command "COMMAND -- DIR/PATH" for each path, quoted for the shell.
print_commands() {
  local cmd=$1 dir=$2
  local f
  while IFS= read -r -d '' f; do
    printf '%s -- %q\n' "$cmd" "$dir/$f"
  done
}

# Usage: print_fjalar_removals < PATHS
# Like print_commands "git rm --ignore-unmatch" valgrind/fjalar, but for a
# file that is still in the work tree, prints a comment instead.  Such a
# file may contain Fjalar changes, so the user must check it before
# removing it; see doc/valgrind-merge.texinfo.
print_fjalar_removals() {
  local f
  while IFS= read -r -d '' f; do
    if [ -e "$fjalar/valgrind/fjalar/$f" ] || [ -L "$fjalar/valgrind/fjalar/$f" ]; then
      printf '# Valgrind removed %q.  Check it for Fjalar changes, then run:\n' \
        "valgrind/fjalar/$f"
      printf '# git rm -- %q\n' "valgrind/fjalar/$f"
      echo "$0: Valgrind removed valgrind/fjalar/$f; check it for Fjalar changes." >&2
    else
      printf '%s -- %q\n' "git rm --ignore-unmatch" "valgrind/fjalar/$f"
    fi
  done
}

print_commands "git add" valgrind < "$tmpdir/added"
print_commands "git rm --ignore-unmatch" valgrind < "$tmpdir/removed"
# Fjalar's modified copy of Memcheck is in valgrind/fjalar/.
memcheck_files < "$tmpdir/added" | print_commands "git add" valgrind/fjalar
memcheck_files < "$tmpdir/removed" | print_fjalar_removals
