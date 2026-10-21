#!/bin/bash

# This script checks that a merge by merge-valgrind.sh kept each of Fjalar's
# changes to upstream Valgrind; see doc/valgrind-merge.texinfo.  A merge can
# lose a change without reporting a conflict.
# Usage: compare-fjalar-changes.sh
# Run it after resolving the conflicts, in the Fjalar tree that contains this
# script.  It compares Fjalar's changes to the base Valgrind before the merge
# (from refs/valgrind-merge/base to refs/valgrind-merge/fjalar) with Fjalar's
# changes to the target Valgrind after the merge (from refs/valgrind-merge/new
# to the index), and prints the differences.  It ignores unstaged changes, and
# the files that only Fjalar has, as $INV/coregrind-Fjalar.diff and
# $INV/memcheck-Fjalar.diff do.
#
# The output is that of "git range-diff":  a diff of the two diffs.  A line
# that starts with "-" followed by "+" or "-" is part of a change that the
# merge lost or altered, and a line that starts with "+" followed by "+" or
# "-" is part of a change that the merge or the conflict resolution added.
# Some differences are expected:  a change that upstream also made is no
# longer one of Fjalar's changes, and a change that was adapted to upstream's
# changes differs.  The script exits with status 1 if there are differences.

set -e
set -o pipefail
# Make a failure inside a command substitution stop the script.
shopt -s inherit_errexit

if [ $# -ne 0 ]; then
  echo "Usage: $0" >&2
  exit 2
fi

# The Fjalar tree that contains this script, even if $0 is a symbolic link.
fjalar=$(dirname -- "$(readlink -f -- "$0")")
cd "$fjalar"

for ref in base new fjalar; do
  if ! git rev-parse --verify -q "refs/valgrind-merge/$ref" > /dev/null; then
    echo "$0: refs/valgrind-merge/$ref does not exist; run merge-valgrind.sh first." >&2
    exit 1
  fi
done
if ! merged_tree=$(git write-tree 2> /dev/null); then
  echo "$0: resolve the conflicts first; these files are unmerged:" >&2
  git diff --name-only --diff-filter=U >&2
  exit 1
fi

tmpindex=$(mktemp)
trap 'rm -f "$tmpindex"' EXIT

# Usage: changes_commit PARENT TREE
# Prints the name of a new commit, with parent PARENT, that makes Fjalar's
# changes to PARENT's files:  the changes from PARENT to TREE, except for
# adding files.  The options make the diff independent of the user's Git
# configuration.
changes_commit() {
  local parent=$1 tree=$2
  rm -f "$tmpindex"
  GIT_INDEX_FILE=$tmpindex git read-tree "$parent"
  git diff --binary --full-index --no-renames --no-ext-diff --no-textconv \
      --no-color --diff-filter=a "$parent" "$tree" -- valgrind \
    | GIT_INDEX_FILE=$tmpindex git apply --cached --allow-empty --whitespace=nowarn
  # The commits are only for the comparison, so they need no signature.  The
  # same message for both keeps it out of the comparison.
  git commit-tree --no-gpg-sign "$(GIT_INDEX_FILE=$tmpindex git write-tree)" \
    -p "$parent" -m "Fjalar's changes to Valgrind"
}

before=$(changes_commit refs/valgrind-merge/base "refs/valgrind-merge/fjalar^{tree}")
after=$(changes_commit refs/valgrind-merge/new "$merged_tree")

# A large creation factor makes "git range-diff" compare the two commits even
# if they differ greatly, rather than report one as removed and the other as
# added.  With the default diff algorithm, the comparison can misalign the
# diffs of whole files, and report a file's changes as both lost and added.
comparison=$(git range-diff --no-color --creation-factor=1000 --diff-algorithm=histogram \
  "refs/valgrind-merge/base..$before" "refs/valgrind-merge/new..$after")
# The first line has "=" between the two commits if their changes are the same.
if [[ "$(head -n 1 <<< "$comparison")" =~ ^[0-9]+:\ +[0-9a-f]+\ =\  ]]; then
  echo "$0: the merge kept Fjalar's changes unaltered."
  exit 0
fi
echo "$comparison"
exit 1
