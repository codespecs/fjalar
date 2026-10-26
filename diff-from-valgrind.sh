#!/bin/bash

# This script prints the differences between the Fjalar tree that contains
# this script and the upstream Valgrind release that Fjalar is based on.
# Every one of them is a potential conflict in the next Valgrind merge; see
# doc/valgrind-merge.texinfo.
#
# Usage: diff-from-valgrind.sh [--valgrind=DIR] [GIT-DIFF-OPTION...] [-- PATH...]
#   DIR is a git clone of upstream Valgrind, at the release that
#   valgrind/REVISION names; the default is $INV/valgrind-old.
#   Each GIT-DIFF-OPTION, such as --stat, --numstat, or -w, is passed to
#   "git diff".
#   Each PATH, relative to the top of the Fjalar tree, limits the diff to
#   that file or directory; the default is valgrind.
#
# The output is a diff from the tree that merge-valgrind.sh uses as the base
# of a merge (upstream's tree at valgrind/, and upstream's Memcheck at
# valgrind/fjalar/) to Fjalar's HEAD.  It omits the files that only Fjalar
# has, such as Fjalar's own sources and the files from Binutils, and
# includes the files that only upstream has.

set -e
set -o pipefail
# Make a failure inside a command substitution stop the script.
shopt -s inherit_errexit

# Make "cd" with a relative directory resolve it against the current
# directory.
unset CDPATH

valgrind=
options=()
paths=(valgrind)
while [ $# -gt 0 ]; do
  case $1 in
    --valgrind=*) valgrind=${1#--valgrind=} ;;
    --)
      shift
      paths=("$@")
      break
      ;;
    *) options+=("$1") ;;
  esac
  shift
done
if [ -z "$valgrind" ]; then
  if [ -z "$INV" ]; then
    echo "$0: INV is not set, and --valgrind is not given; see doc/valgrind-merge.texinfo." >&2
    exit 1
  fi
  valgrind=$INV/valgrind-old
fi
# Make the directory absolute, because the paths below are used after the
# "cd".
if ! dir=$(cd "$valgrind" && pwd -P); then
  echo "$0: cannot change to directory $valgrind." >&2
  exit 1
fi
valgrind=$dir
# The Fjalar tree that contains this script, even if $0 is a symbolic link.
fjalar=$(dirname -- "$(readlink -f -- "$0")")

source "$fjalar/valgrind-common.sh"

check_toplevel "$fjalar"
check_toplevel "$valgrind"

cd "$fjalar"

# A clone of another release, such as one left over from a merge, would
# make the diff include upstream's changes between the two releases.
tag=$(valgrind_release_tag)
if ! tag_commit=$(git -C "$valgrind" rev-parse --verify -q "refs/tags/$tag^{commit}") \
    || [ "$(git -C "$valgrind" rev-parse HEAD)" != "$tag_commit" ]; then
  echo "$0: $valgrind is not at tag $tag, the release that valgrind/REVISION names." >&2
  exit 1
fi

tmpindex=$(mktemp)
trap 'rm -f "$tmpindex"' EXIT

base=$(upstream_tree "$valgrind")
# --diff-filter=a omits the files that only Fjalar has.  With rename
# detection, a file that only Fjalar has could appear as a rename of a file
# that only upstream has.
git diff --no-renames --diff-filter=a "${options[@]}" "$base" HEAD -- "${paths[@]}"
