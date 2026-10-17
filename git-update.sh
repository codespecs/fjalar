#!/bin/bash
# Prints the commands that add and remove files as a result of a Valgrind
# merge.  Review the output, then run it with "bash -ev".
# Run this in $INV/fjalar, after applying ../coregrind.patch and
# ../memcheck.patch.  It compares ../valgrind-old with ../valgrind-new, the
# directories that generate-patch-files.sh diffs.
#  * patch does not handle binary files or create empty files, so the output
#    copies them.
#  * Fjalar's copy of memcheck is valgrind/fjalar/, not valgrind/memcheck/.
#    A memcheck file that upstream removed may contain Fjalar changes, so its
#    "git rm" command is commented out.

set -euo pipefail
# comm requires the collation order that sort uses, and grep -I should treat
# only NUL bytes, not invalid UTF-8, as binary.
export LC_ALL=C

for dir in ../valgrind-old ../valgrind-new valgrind/fjalar; do
  if [ ! -d "$dir" ]; then
    echo "$0: no directory $dir; run this in \$INV/fjalar" >&2
    exit 1
  fi
done

# Prints the paths under directory $1, relative to it, sorted.  Omits .git and
# the basenames given as the remaining arguments, as "diff -x" does.
list_files() {
  local dir=$1
  shift
  local prune=(-name .git)
  local name
  for name in "$@"; do
    prune+=(-o -name "$name")
  done
  (cd "$dir" && find . -mindepth 1 \( "${prune[@]}" \) -prune -o -print) \
    | sed 's|^\./||' | sort
}

# Reads sorted paths, and prints each one whose parent directory was not read.
topmost() {
  awk '{ p = $0; top = 1
         while (sub(/\/[^\/]*$/, "", p)) if (p in seen) { top = 0; break }
         seen[$0]
         if (top) print }'
}

# Prints the commands that apply the file additions and removals from
# directory $1 to directory $2, to directory $3.  $4 is prepended to each
# "git rm" command, which ignores paths that were already removed.  The remaining arguments are basenames to omit.
print_commands() {
  local old=$1 new=$2 dest=$3 rm_prefix=$4
  shift 4
  local f

  echo "# Binary files added or changed upstream, and empty files added upstream"
  list_files "$new" "$@" | while IFS= read -r f; do
    [ -f "$new/$f" ] || continue
    if { [ -s "$new/$f" ] && ! grep -qI '' "$new/$f" \
           && ! cmp -s "$old/$f" "$new/$f" 2>/dev/null; } \
       || { [ ! -s "$new/$f" ] && [ ! -e "$old/$f" ]; }; then
      printf 'mkdir -p -- %q\n' "$(dirname "$dest/$f")"
      printf 'cp -p -- %q %q\n' "$new/$f" "$dest/$f"
    fi
  done

  echo "# Files and directories added upstream"
  comm -13 <(list_files "$old" "$@") <(list_files "$new" "$@") | topmost \
    | while IFS= read -r f; do
        printf 'git add -- %q\n' "$dest/$f"
      done

  echo "# Files and directories removed upstream"
  comm -23 <(list_files "$old" "$@") <(list_files "$new" "$@") | topmost \
    | while IFS= read -r f; do
        printf '%sgit rm -r --ignore-unmatch -- %q\n' "$rm_prefix" "$dest/$f"
      done
}

echo "### Everything except Fjalar's copy of memcheck"
print_commands ../valgrind-old ../valgrind-new valgrind ""
echo
echo "### Fjalar's copy of memcheck; uncomment each \"git rm\" after checking it"
print_commands ../valgrind-old/memcheck ../valgrind-new/memcheck valgrind/fjalar "# " docs tests
