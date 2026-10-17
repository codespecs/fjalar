#!/bin/bash

# This script applies a patch file that generate-patch-files.sh created to
# $INV/fjalar with a 3-way merge, stages the result, and lists the conflicts.
# Usage: apply-patch-files.sh [--check] coregrind|memcheck [GIT-APPLY-OPTION...]
# With --check, it does a dry run, which changes no file in the work tree or
# the index, though it does add objects to the Fjalar repository and
# overwrite the log file.
# Each GIT-APPLY-OPTION, such as --exclude=PATH, is passed to "git apply"
# after the default options, so it overrides them.
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

# A clean work tree and index keep the merge separate from other changes,
# so "git reset --hard" can undo it.  A dry run requires them too, because
# option --3way implies --index, so "git apply --check" would refuse every
# file whose work-tree version differs from its index version.
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "$0: $INV/fjalar has uncommitted changes; commit them first." >&2
  exit 1
fi

# The "index" lines of the patch name blobs of valgrind-old, which --3way
# needs as the merge base.  Copy them into the Fjalar repository, so that
# "git mergetool" can use them after this script exits.  An alternate object
# directory would not suffice:  "git apply" would not write a merged blob
# that exists in the alternate, so the index would name a missing object.
sed -n 's/^index \([0-9a-f]\{40,\}\)\.\.[0-9a-f]\{40,\}.*/\1/p' "$patch" \
  | sed '/^0*$/d' | sort -u \
  | git -C "$INV/valgrind-old" pack-objects -q --stdout | git unpack-objects -q \
  || { echo "$0: could not copy blobs from $INV/valgrind-old." >&2; exit 1; }
# The messages of "git apply" are parsed below, so they must be in English.
export LC_ALL=C

# Option --3way implies --index, so "git apply" stages the files that it
# changes, creates, or removes, even ones that match .gitignore.  A file that
# it cannot merge, such as a binary file, is left with the Fjalar version.
# Option --whitespace=nowarn overrides any apply.whitespace setting, which
# could otherwise strip whitespace from lines that upstream added.
# Option --no-ignore-whitespace overrides any apply.ignoreWhitespace setting.
apply=(git apply --3way --whitespace=nowarn --no-ignore-whitespace "$strip" --directory="$directory")

# A patch to a file that changes only its mode has no "index" line, so
# "git apply --3way" reports an error, falls back to direct application, and
# succeeds.  The base blobs of all other patches were copied above, so this
# sed command removes only messages about successful mode changes.
quiet_mode_changes='/^error: repository lacks the necessary blob to perform 3-way merge\.$/{N;/\nFalling back to direct application\.\.\.$/d}'

# "git apply" applies no patch at all if it refuses the patch to any file.
# Examples are a removal of a file that Fjalar has changed and a change to a
# file that does not exist.  A dry run finds those files, so that the
# actual run can exclude them.
status=0
"${apply[@]}" --check "$@" "$patch" 2>&1 | sed "$quiet_mode_changes" > "$log" || status=$?
# For each refused file, "refused" holds its name and "reasons" holds the
# message that gives the name and the reason.
refused=()
reasons=()
while IFS= read -r line; do
  if [[ $line =~ ^error:\ (.+):\ [^:]+$ ]] && [[ $line != "error: patch failed: "* ]]; then
    refused+=("${BASH_REMATCH[1]}")
    reasons+=("${line#error: }")
  fi
done < "$log"
if [ "$status" -ne 0 ] && [ ${#refused[@]} -eq 0 ]; then
  cat "$log"
  echo "$0: git apply failed; see $log." >&2
  exit 1
fi

if [ -n "$check" ]; then
  cat "$log"
  conflicts=$(sed -n "s/^Applied patch to '\(.*\)' with conflicts\.\$/\1/p" "$log")
else
  exclude=()
  for file in "${refused[@]}"; do
    # Option --exclude takes a glob pattern.
    exclude+=("--exclude=$(printf '%s' "$file" | sed 's/[][*?\\]/\\&/g')")
  done
  status=0
  "${apply[@]}" "${exclude[@]}" "$@" "$patch" 2>&1 | sed "$quiet_mode_changes" | tee "$log" \
    || status=$?
  if [ "$status" -ne 0 ] && [ -z "$(git ls-files -u)" ]; then
    echo "$0: git apply failed; see $log." >&2
    exit 1
  fi
  conflicts=$(git diff --name-only --diff-filter=U)
fi

if [ -z "$conflicts" ] && [ ${#refused[@]} -eq 0 ]; then
  exit 0
fi
# The summary is also appended to the log, which otherwise would not give
# the reasons that the dry run found for refusing files.
{
  echo
  if [ -n "$check" ]; then
    echo "$0: the dry run found these conflicts."
  else
    echo "$0: Resolve these conflicts."
  fi
  if [ -n "$conflicts" ]; then
    echo "Files with conflicts:"
    echo "$conflicts"
  fi
  if [ ${#refused[@]} -gt 0 ]; then
    echo "Files whose patches were not applied, and why:"
    printf '%s\n' "${reasons[@]}"
  fi
} | tee -a "$log"
exit 1
