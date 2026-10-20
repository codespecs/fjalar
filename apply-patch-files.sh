#!/bin/bash

# This script applies a patch file that generate-patch-files.sh created to
# the Fjalar tree that contains this script, which need not be $INV/fjalar,
# with a 3-way merge, stages the result, and lists the conflicts.
# Usage: apply-patch-files.sh [--check] coregrind|memcheck [GIT-APPLY-OPTION...]
# With --check, it does a dry run, which changes no file in the work tree or
# the index, though it does add objects to the Fjalar repository and
# overwrite the log file and, for memcheck, write $INV/fjalar-Makefile.am.
# Each GIT-APPLY-OPTION, such as --exclude=PATH, is passed to "git apply"
# after the default options, so it overrides them.
# Options that reduce the context, such as -C0, do not reduce the conflicts:
# "git apply --3way" applies each patch by a 3-way merge, which ignores
# them.  They take effect only when "git apply" falls back to direct
# application, where they risk applying a patch at the wrong place.
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
makefile_problems=
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
# Option --check passed through to "git apply" would apply nothing, but the
# script would still stage the merge results.
for arg in "$@"; do
  if [ "$arg" = "--check" ]; then
    echo "$usage" >&2
    exit 1
  fi
done

if [ -z "$INV" ]; then
  echo "$0: INV is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi
# Make INV absolute, because the paths below are used after the "cd".
if ! inv=$(cd "$INV" && pwd -P); then
  echo "$0: cannot change to directory $INV." >&2
  exit 1
fi
INV=$inv
# The Fjalar tree that contains this script.
fjalar="$(cd "$(dirname "$0")" && pwd -P)"
# Without this check, the git commands below would operate on an enclosing
# repository, or would fail.
if [ "$(git -C "$fjalar" rev-parse --show-toplevel 2> /dev/null)" != "$fjalar" ]; then
  echo "$0: $fjalar is not the top level of a git clone." >&2
  exit 1
fi
patch=$INV/$name.patch
log=$INV/$name-apply.log
if [ ! -f "$patch" ]; then
  echo "$0: $patch does not exist; run generate-patch-files.sh." >&2
  exit 1
fi
cd "$fjalar"

# A clean work tree and index keep the merge separate from other changes,
# so "git reset --hard" can undo it.  A dry run requires them too, because
# option --3way implies --index, so "git apply --check" would refuse every
# file whose work-tree version differs from its index version.
# A failure of a command substitution in a condition does not stop the
# script, so check git's exit status separately.
if ! changes=$(git status --porcelain --untracked-files=no); then
  echo "$0: git status failed in $fjalar." >&2
  exit 1
fi
if [ -n "$changes" ]; then
  echo "$0: $fjalar has uncommitted changes; commit them first." >&2
  exit 1
fi

# The "index" lines of the patch name blobs of valgrind-old, which --3way
# needs as the merge base.  Copy them into the Fjalar repository, so that
# "git mergetool" can use them after this script exits.  An alternate object
# directory would not suffice:  "git apply" would not write a merged blob
# that exists in the alternate, so the index would name a missing object.
sed -n '/^index 0*\.\./d; s/^index \([0-9a-f]\{40,\}\)\.\.[0-9a-f]\{40,\}.*/\1/p' "$patch" \
  | sort -u \
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
# With rerere.autoupdate, "git apply" fails when rerere tries to stage a file
# that it resolves from a recorded resolution.  Without rerere.autoupdate,
# rerere writes the resolution to the work tree but leaves the file unmerged,
# so the file is listed with the conflicts.
apply=(git -c rerere.autoupdate=false apply --3way --whitespace=nowarn --no-ignore-whitespace "$strip" --directory="$directory")

# "git apply --3way" falls back to direct application for a patch that
# creates or removes a file, and for a patch that changes only the mode of a
# file, because that patch has no "index" line.  For the latter, it also
# reports an error.  The base blobs of all other patches were copied above,
# so this sed command removes only messages about those fallbacks, which
# name no file.  If direct application fails, "git apply" reports that
# separately.
quiet_fallbacks='/^error: repository lacks the necessary blob to perform 3-way merge\.$/d; /^Falling back to direct application\.\.\.$/d'

# "git apply" applies no patch at all if it refuses the patch to any file.
# Examples are a removal of a file that Fjalar has changed and a change to a
# file that does not exist.  A dry run finds those files, so that the
# actual run can exclude them.
status=0
"${apply[@]}" --check "$@" "$patch" 2>&1 | sed "$quiet_fallbacks" > "$log" || status=$?
# For each refused file, "refused" holds its name and "reasons" holds the
# message that gives the name and the reason.  "other_errors" holds the
# error messages that name no file, which the summary of a dry run lists.
refused=()
reasons=()
other_errors=()
while IFS= read -r line; do
  if [[ $line =~ ^error:\ (.+):\ [^:]+$ ]]; then
    refused+=("${BASH_REMATCH[1]}")
    reasons+=("${line#error: }")
  elif [[ $line == error:* ]]; then
    other_errors+=("$line")
  fi
done < "$log"
# Print the files that the dry run refused and the reasons.
print_refused() {
  echo "Files whose patches were not applied, and why:"
  printf '%s\n' "${reasons[@]}"
}
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
  "${apply[@]}" "${exclude[@]}" "$@" "$patch" 2>&1 | sed "$quiet_fallbacks" | tee "$log" \
    || status=$?
  conflicts=$(git diff --name-only --diff-filter=U)
  if [ "$status" -ne 0 ] && [ -z "$conflicts" ]; then
    # The log of the dry run, which gave the reasons, was overwritten.
    if [ ${#refused[@]} -gt 0 ]; then
      { echo; print_refused; } | tee -a "$log"
    fi
    echo "$0: git apply failed; see $log." >&2
    exit 1
  fi
fi

# memcheck.patch omits memcheck/Makefile.am.  Instead, generate Fjalar's
# version from Memcheck's, which the Coregrind merge updated.  A dry run
# writes it to $INV/fjalar-Makefile.am instead.  If the generator fails or
# finds problems, the file is not staged, so that it is not marked as
# resolved; the summary below still lists the conflicts and refused files.
if [ "$name" = memcheck ]; then
  if [ -n "$check" ]; then
    makefile=$INV/fjalar-Makefile.am
  else
    makefile=valgrind/fjalar/Makefile.am
  fi
  status=0
  makefile_problems=$("$fjalar/generate-fjalar-makefile.sh" "$makefile") || status=$?
  if [ "$status" -ne 0 ] && [ "$status" -ne 2 ]; then
    makefile_problems="generate-fjalar-makefile.sh failed; fix the problem and rerun it."
  fi
  if [ -z "$check" ]; then
    if [ -z "$makefile_problems" ]; then
      git add valgrind/fjalar/Makefile.am
    else
      makefile_problems="$makefile_problems"$'\n'"valgrind/fjalar/Makefile.am is not staged."
    fi
  fi
fi

if [ -z "$conflicts" ] && [ ${#refused[@]} -eq 0 ] && [ -z "$makefile_problems" ]; then
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
    print_refused
  fi
  if [ -n "$check" ] && [ ${#other_errors[@]} -gt 0 ]; then
    echo "Other errors, which may make the actual merge fail:"
    printf '%s\n' "${other_errors[@]}"
  fi
  if [ -n "$makefile_problems" ]; then
    echo "$makefile_problems"
  fi
} | tee -a "$log"
exit 1
