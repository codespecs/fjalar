# shellcheck shell=bash

# This file defines what merge-valgrind.sh, upstream-regtest.sh, and
# diff-from-valgrind.sh have in common.  Each of them sources it.

# Without this check, git commands on DIR would operate on an enclosing
# repository, or would fail.
# Usage: check_toplevel DIR
check_toplevel() {
  local dir=$1 toplevel
  toplevel=$(git -C "$dir" rev-parse --show-toplevel 2> /dev/null) || toplevel=
  if [ -z "$toplevel" ] || [ "$toplevel" != "$(cd -- "$dir" 2> /dev/null && pwd -P)" ]; then
    echo "$0: $dir is not the top level of a git clone." >&2
    exit 1
  fi
}

# At the next merge, it is easy to forget to move valgrind-new to
# valgrind-old, or to clone the wrong tag.
# Usage: check_tag DIR TAG_VARIABLE
# If variable TAG_VARIABLE is set, checks that DIR is at the tag that is the
# variable's value.
check_tag() {
  local dir=$1 var=$2
  local tag=${!var}
  local commit
  if [ -z "$tag" ]; then
    return
  fi
  if ! commit=$(git -C "$dir" rev-parse --verify -q "refs/tags/$tag^{commit}"); then
    echo "$0: $dir has no tag $tag (the value of $var)." >&2
    exit 1
  fi
  if [ "$(git -C "$dir" rev-parse HEAD)" != "$commit" ]; then
    echo "$0: $dir is not at tag $tag (the value of $var)." >&2
    exit 1
  fi
}

# Usage: valgrind_release_tag
# Prints the tag of the upstream Valgrind release that HEAD's
# valgrind/REVISION names, such as VALGRIND_3_23_0.  Run it in a Fjalar tree.
valgrind_release_tag() {
  local version
  version=$(git show HEAD:valgrind/REVISION \
    | sed -n 's/^# Valgrind version \([0-9][0-9.]*[0-9]\),.*/\1/p')
  if [ -z "$version" ] || [ "$(wc -l <<< "$version")" -ne 1 ]; then
    echo "$0: valgrind/REVISION does not name a Valgrind version." >&2
    exit 1
  fi
  echo "VALGRIND_${version//./_}"
}

# Usage: upstream_tree DIR
# Prints the name of a tree that has the tree of DIR's HEAD at valgrind/, and
# that tree's memcheck/, without docs/, tests/, and Makefile.am, at
# valgrind/fjalar/, where Fjalar keeps its modified copy of Memcheck.
# generate-fjalar-makefile.sh generates Fjalar's version of
# memcheck/Makefile.am, so the tree omits it.  Run it in a Fjalar tree, which
# gets the tree and its objects.  It uses the file that variable tmpindex
# names as a temporary index, and removes that file.
# shellcheck disable=SC2154 # The caller sets tmpindex.
upstream_tree() {
  local dir=$1 tree
  tree=$(git -C "$dir" rev-parse "HEAD^{tree}")
  # Copy the tree's objects into the Fjalar repository, unless an earlier
  # call copied them, which it did if the tree is there.  "git fetch" would
  # fail for a shallow clone, and would also copy upstream's history.
  # "git index-pack" stores them as one pack, rather than as thousands of
  # loose objects, and prints the pack's name.
  if ! git cat-file -e "$tree" 2> /dev/null; then
    git -C "$dir" rev-list --objects "$tree" | cut -d' ' -f1 \
      | git -C "$dir" pack-objects -q --stdout | git index-pack --stdin > /dev/null
  fi
  rm -f "$tmpindex"
  GIT_INDEX_FILE=$tmpindex git read-tree --prefix=valgrind/ "$tree"
  GIT_INDEX_FILE=$tmpindex git read-tree --prefix=valgrind/fjalar/ "$tree:memcheck"
  GIT_INDEX_FILE=$tmpindex git rm -q -r -f --cached --ignore-unmatch -- \
    valgrind/fjalar/docs valgrind/fjalar/tests valgrind/fjalar/Makefile.am
  GIT_INDEX_FILE=$tmpindex git write-tree
  rm -f "$tmpindex"
}
