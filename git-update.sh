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


# Usage: print_command COMMAND < PATHS
# Prints one command "COMMAND -- PATH..." that names every path, one per
# line, quoted for the shell.  Prints nothing if there are no paths.
print_command() {
  local cmd=$1
  local f first=true
  while IFS= read -r -d '' f; do
    if $first; then
      printf '%s --' "$cmd"
      first=false
    fi
    printf ' \\\n  %q' "$f"
  done
  if ! $first; then
    echo
  fi
}

# Usage: print_additions SRCDIR DIR < PATHS
# Prints the commands that add DIR/PATH for each path, where SRCDIR/PATH is
# the file in valgrind-new.  The patch files cannot create an empty file or a
# binary file, because diff prints nothing for a new empty file and prints only
# "Binary files ... differ" for a new binary file.  So for each file that is
# not in the work tree, first prints a command that copies it from SRCDIR.
# "git add -f" adds a file even if it matches Fjalar's .gitignore, which
# ignores names such as Makefile that some Valgrind files have.
print_additions() {
  local srcdir=$1 dir=$2
  local f
  : > "$tmpdir/paths"
  while IFS= read -r -d '' f; do
    if [ ! -e "$fjalar/$dir/$f" ] && [ ! -L "$fjalar/$dir/$f" ]; then
      printf 'mkdir -p -- %q && cp -P -- %q %q\n' \
        "$(dirname "$dir/$f")" "$srcdir/$f" "$dir/$f"
    fi
    printf '%s\0' "$dir/$f" >> "$tmpdir/paths"
  done
  print_command "git add -f" < "$tmpdir/paths"
}

# Usage: print_removals OLDDIR DIR < PATHS
# Prints the commands that remove DIR/PATH for each path, where OLDDIR/PATH is
# the file in valgrind-old.  The patch files leave removed files alone, so a
# file that is still in the work tree and differs from OLDDIR/PATH contains
# Fjalar changes.  For such a file, prints a comment instead, so that the user
# checks it before removing it.  "git rm --ignore-unmatch" succeeds even if
# the user already ran "git rm" on a file.
print_removals() {
  local olddir=$1 dir=$2
  local f
  : > "$tmpdir/paths"
  while IFS= read -r -d '' f; do
    if { [ -e "$fjalar/$dir/$f" ] || [ -L "$fjalar/$dir/$f" ]; } \
       && ! cmp -s -- "$olddir/$f" "$fjalar/$dir/$f"; then
      printf '# Valgrind removed %q, which has Fjalar changes.  Check it, then run:\n' \
        "$dir/$f"
      printf '# git rm -- %q\n' "$dir/$f"
      echo "$0: Valgrind removed $dir/$f, which has Fjalar changes; check it." >&2
    else
      printf '%s\0' "$dir/$f" >> "$tmpdir/paths"
    fi
  done
  print_command "git rm --ignore-unmatch" < "$tmpdir/paths"
}

print_additions "$INV/valgrind-new" valgrind < "$tmpdir/added"
print_removals "$INV/valgrind-old" valgrind < "$tmpdir/removed"
# Fjalar's modified copy of Memcheck is in valgrind/fjalar/.
memcheck_files < "$tmpdir/added" \
  | print_additions "$INV/valgrind-new/memcheck" valgrind/fjalar
memcheck_files < "$tmpdir/removed" \
  | print_removals "$INV/valgrind-old/memcheck" valgrind/fjalar
