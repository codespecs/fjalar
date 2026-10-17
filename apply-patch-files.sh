#!/bin/bash

# This script applies a patch file that generate-patch-files.sh created to
# $INV/fjalar, stages the result, and lists the conflicts.
# Usage: apply-patch-files.sh [--check] coregrind|memcheck [GIT-APPLY-OPTION...]
# With --check, it does a dry run and does not change any file.
# Each GIT-APPLY-OPTION, such as -C0, is passed to "git apply" after the
# default options, so it overrides them.
# The output of "git apply" is also written to $INV/coregrind-apply.log or
# $INV/memcheck-apply.log.  The script exits with status 1 if there were
# conflicts or other problems.

set -e
set -o pipefail

# Make "cd" with a relative directory resolve it against the current
# directory.
unset CDPATH

usage="Usage: $0 [--check] coregrind|memcheck [GIT-APPLY-OPTION...]"

check=
if [ "$1" = "--check" ]; then
  check=--check
  shift
fi
case "$1" in
  coregrind) strip=-p2 directory=valgrind ;;
  memcheck) strip=-p3 directory=valgrind/fjalar ;;
  *)
    echo "$usage" >&2
    exit 1
    ;;
esac
name=$1
shift

if [ -z "$INV" ]; then
  echo "$0: INV is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi
patch=$INV/$name.patch
log=$INV/$name-apply.log
if [ ! -f "$patch" ]; then
  echo "$0: $patch does not exist; run generate-patch-files.sh." >&2
  exit 1
fi
cd "$INV/fjalar"

# Option -C1 requires only one line of context around each change to match,
# like the default fuzz factor of "patch".  Option --whitespace=nowarn
# overrides any apply.whitespace setting, which could otherwise strip
# whitespace from lines that upstream added.
apply=(git apply --whitespace=nowarn -C1 "$strip" --directory="$directory")

if [ -n "$check" ]; then
  "${apply[@]}" --check "$@" "$patch"
  exit
fi

# The files that the patch creates.  A file that already exists is omitted,
# because "git apply" refuses to overwrite it.
created=()
while IFS= read -r file; do
  if [ ! -e "$file" ]; then
    created+=("$file")
  fi
done < <(git -c core.quotePath=false apply --summary "$strip" --directory="$directory" "$patch" \
           | sed -n 's/^ create mode [0-7]* //p')

status=0
"${apply[@]}" --reject "$@" "$patch" 2>&1 | tee "$log" || status=$?

# "git add -u" stages the changed and removed files.  The created files are
# staged with "git add -f", because some of them, such as Makefile or *.log
# files, match patterns in .gitignore.
git add -u "$directory"
if [ ${#created[@]} -gt 0 ]; then
  git add -f -- "${created[@]}"
fi

if [ "$status" -eq 0 ]; then
  exit 0
fi

# A hunk that does not apply is put in a .rej file.  A patch that
# "git apply" refuses entirely leaves no .rej file.
rejects=$(find "$directory" -name '*.rej')
refused=$(grep '^error: ' "$log" | grep -v -e 'while searching for' -e 'patch failed' || true)
echo
echo "$0: git apply exited with status $status.  Resolve these conflicts."
if [ -n "$rejects" ]; then
  echo "Rejected hunks:"
  echo "$rejects"
fi
if [ -n "$refused" ]; then
  echo "Patches that were not applied:"
  echo "$refused"
fi
if [ -z "$rejects" ] && [ -z "$refused" ]; then
  echo "No .rej file or refused patch was found; see $log."
fi
exit 1
