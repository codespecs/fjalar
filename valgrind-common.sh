# shellcheck shell=bash

# This file defines what merge-valgrind.sh and upstream-regtest.sh have in
# common.  Each of them sources it.

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
