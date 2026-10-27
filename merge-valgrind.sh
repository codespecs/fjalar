#!/bin/bash

# This script merges a newer version of upstream Valgrind into the Fjalar
# tree that contains this script, which need not be $INV/fjalar; see
# doc/valgrind-merge.texinfo.
# Usage: merge-valgrind.sh [CHERRY-PICK-OPTION...]
# The base of the merge is the commit checked out in $INV/valgrind-old, and
# the target is the commit checked out in $INV/valgrind-new.  The script
# checks that valgrind-old is at tag VOLDTAG, which by default is the release
# that valgrind/REVISION names, and, if VNEWTAG is set, that valgrind-new is
# at tag VNEWTAG.
#
# The script records Fjalar's HEAD as ref refs/valgrind-merge/fjalar, and
# creates two commits, which it records as refs
# refs/valgrind-merge/base and refs/valgrind-merge/new.  Each has upstream's
# tree at valgrind/ and upstream's Memcheck at valgrind/fjalar/, where Fjalar
# keeps its modified copy of Memcheck, without Memcheck's docs, tests, and
# Makefile.am.  Then the script runs "git cherry-pick --no-commit" of
# refs/valgrind-merge/new, which merges upstream's changes into Fjalar by a
# 3-way merge whose base is refs/valgrind-merge/base.  Each
# CHERRY-PICK-OPTION, such as -Xno-renames, is passed to "git cherry-pick".
# Files that only Fjalar has are in neither commit, so the merge leaves them
# unchanged.
#
# Then the script generates valgrind/fjalar/Makefile.am with
# generate-fjalar-makefile.sh, and stages it unless the generator reports a
# problem.  It lists the files with conflicts, and exits with status 1 if
# there are conflicts or other problems.
#
# A merge can lose one of Fjalar's changes without reporting a conflict.
# compare-fjalar-changes.sh checks that the merge kept each of them.

set -e
set -o pipefail
# Make a failure inside a command substitution stop the script.
shopt -s inherit_errexit

# Make "cd" with a relative directory resolve it against the current
# directory.
unset CDPATH

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
# The Fjalar tree that contains this script, even if $0 is a symbolic link.
fjalar=$(dirname -- "$(readlink -f -- "$0")")

source "$fjalar/valgrind-common.sh"

check_toplevel "$fjalar"
check_toplevel "$INV/valgrind-old"
check_toplevel "$INV/valgrind-new"
# Until the merge is committed, valgrind/REVISION names the release that
# Fjalar is based on, which is the base of the merge.
if [ -n "$VOLDTAG" ]; then
  check_tag "$INV/valgrind-old" "$VOLDTAG" "the value of VOLDTAG"
else
  oldtag=$(cd "$fjalar" && valgrind_release_tag)
  check_tag "$INV/valgrind-old" "$oldtag" "the release that valgrind/REVISION names"
fi
check_tag "$INV/valgrind-new" "$VNEWTAG" "the value of VNEWTAG"

# The merge uses the committed trees of the upstream clones, so build
# products in them do no harm, but a change to a tracked file would be
# silently ignored.  A clean Fjalar work tree and index keep the merge
# separate from other changes, so "git reset --hard" can undo it.
# Usage: check_unchanged DIR
check_unchanged() {
  local dir=$1 changes
  changes=$(git -C "$dir" status --porcelain --untracked-files=no)
  if [ -n "$changes" ]; then
    echo "$0: $dir has uncommitted changes:" >&2
    head -n 20 <<< "$changes" >&2
    exit 1
  fi
}
check_unchanged "$INV/valgrind-old"
check_unchanged "$INV/valgrind-new"
check_unchanged "$fjalar"

cd "$fjalar"

# Usage: upstream_commit DIR [PARENT]
# Prints the name of a new commit, with parent PARENT if it is given, whose
# tree is upstream_tree's for DIR.
upstream_commit() {
  local dir=$1 parent=$2 tree
  tree=$(upstream_tree "$dir")
  # The commits are only for the merge, so they need no signature.
  git commit-tree --no-gpg-sign "$tree" ${parent:+-p "$parent"} \
    -m "Valgrind $(git -C "$dir" describe --tags --always)"
}

base_commit=$(upstream_commit "$INV/valgrind-old")
new_commit=$(upstream_commit "$INV/valgrind-new" "$base_commit")
# The refs keep the commits from being garbage-collected, and name them in
# later commands, such as "git diff valgrind-merge/base valgrind-merge/new".
git update-ref refs/valgrind-merge/base "$base_commit"
git update-ref refs/valgrind-merge/new "$new_commit"
# compare-fjalar-changes.sh compares the merge result with Fjalar before the
# merge, which HEAD no longer is if the merge is committed.
git update-ref refs/valgrind-merge/fjalar HEAD

# The options make rename detection independent of the user's Git
# configuration, so that the merge moves Fjalar's changes to a file that
# upstream renamed.  They are Git's defaults, and a CHERRY-PICK-OPTION
# such as -Xno-renames overrides them.  Unless the user has chosen a
# conflict style, each conflict also shows the base Valgrind's text, which
# helps in resolving it.
options=(-c merge.renames=true -c merge.renameLimit=7000
  -c merge.directoryRenames=conflict)
if ! git config --get merge.conflictStyle > /dev/null; then
  options+=(-c merge.conflictStyle=diff3)
fi
status=0
git "${options[@]}" cherry-pick --no-commit "$@" "$new_commit" || status=$?
conflicts=$(git diff --name-only --diff-filter=U)
if [ "$status" -ne 0 ] && [ -z "$conflicts" ]; then
  echo "$0: git cherry-pick failed." >&2
  exit 1
fi

# Generate Fjalar's version of memcheck/Makefile.am from Memcheck's, which
# the merge updated.  If the generator fails or finds problems, the file is
# not staged.
status=0
makefile_problems=$("$fjalar/generate-fjalar-makefile.sh") || status=$?
if [ "$status" -ne 0 ] && [ "$status" -ne 2 ]; then
  makefile_problems="generate-fjalar-makefile.sh failed; fix the problem and rerun it."
fi
if [ -z "$makefile_problems" ]; then
  git add valgrind/fjalar/Makefile.am
else
  makefile_problems="$makefile_problems"$'\n'"valgrind/fjalar/Makefile.am is not staged."
fi

if [ -z "$conflicts" ] && [ -z "$makefile_problems" ]; then
  echo "$0: merged without conflicts; the changes are staged."
  exit 0
fi
echo
if [ -n "$conflicts" ]; then
  echo "$0: Resolve the conflicts in these files:"
  echo "$conflicts"
fi
if [ -n "$makefile_problems" ]; then
  echo "$makefile_problems"
fi
exit 1
