#!/bin/bash

# Clones or updates https://github.com/plume-lib/git-scripts, then prints the
# directory that contains it.  git-scripts provides git-clone-related, which
# clones the Daikon branch that corresponds to this repository's branch.
#
# Usage:  GIT_SCRIPTS="$(clone-git-scripts.sh [DIRECTORY])"
#
# The directory is the argument if one is given and non-empty, otherwise
# $GIT_SCRIPTS if it is set and non-empty, otherwise /tmp/USERNAME/git-scripts,
# where USERNAME is $USER if it is set and non-empty, otherwise `id -un`.

# Fail the whole script if any command fails.
set -e

# Standard output is the return value, so send everything else to standard error.
exec 3>&1 1>&2

if [ "$#" -gt 1 ] ; then
  echo "Usage: $0 [DIRECTORY]" >&2
  exit 2
fi

GIT_SCRIPTS="${1:-${GIT_SCRIPTS:-/tmp/${USER:-$(id -un)}/git-scripts}}"
clone_git_scripts() {
  rm -rf "$GIT_SCRIPTS"
  mkdir -p "$(dirname "$GIT_SCRIPTS")"
  # Retry once, in case of a transient network failure.
  git clone --depth 1 -q https://github.com/plume-lib/git-scripts.git "$GIT_SCRIPTS" \
    || (sleep 1m && git clone --depth 1 -q https://github.com/plume-lib/git-scripts.git "$GIT_SCRIPTS")
}
if git -C "$GIT_SCRIPTS" rev-parse --git-dir > /dev/null 2>&1 ; then
  # An update failure is not fatal; the existing clone is good enough.
  git -C "$GIT_SCRIPTS" pull -q || echo "Warning: cannot update $GIT_SCRIPTS; using it as is." >&2
else
  # The directory does not exist, or a previous clone was interrupted.
  clone_git_scripts
fi

echo "$GIT_SCRIPTS" >&3
