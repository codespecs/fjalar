#!/bin/bash

# Clones or updates https://github.com/plume-lib/git-scripts, then prints the
# directory that contains it.
#
# Usage:  GIT_SCRIPTS="$(clone-git-scripts.sh [DIRECTORY])"
#
# The directory is the argument if one is given and non-empty, otherwise
# $GIT_SCRIPTS if it is set and non-empty, otherwise /tmp/USERNAME/git-scripts.
# USERNAME is $USER if it is set and non-empty, otherwise `id -un`.

# Fail the whole script if any command fails.
set -e

# Standard output is the return value, so send everything else to standard error.
exec 3>&1 1>&2

if [ "$#" -gt 1 ] ; then
  echo "Usage: $0 [DIRECTORY]" >&2
  exit 2
fi

GIT_SCRIPTS="${1:-${GIT_SCRIPTS:-/tmp/${USER:-$(id -un)}/git-scripts}}"
GIT_SCRIPTS_URL=https://github.com/plume-lib/git-scripts.git
if [ -f "$GIT_SCRIPTS/git-clone-related" ] ; then
  # Test for .git in the directory itself; "git -C" would also accept a
  # directory inside some other repository, and then pull that repository.
  if [ -e "$GIT_SCRIPTS/.git" ] ; then
    # An update failure is not fatal; the existing clone is good enough.
    git -C "$GIT_SCRIPTS" pull -q || echo "Warning: cannot update $GIT_SCRIPTS; using it as is." >&2
  fi
else
  if [ -n "$(ls -A "$GIT_SCRIPTS" 2> /dev/null)" ] ; then
    # Delete an interrupted clone of git-scripts, but never any other directory.
    # Read the configuration file directly, because "git config" fails in a
    # repository that has another owner.
    if [ "$(git config --file "$GIT_SCRIPTS/.git/config" --get remote.origin.url 2> /dev/null)" = "$GIT_SCRIPTS_URL" ] ; then
      rm -rf "$GIT_SCRIPTS"
    else
      echo "$0: $GIT_SCRIPTS exists but is not a clone of $GIT_SCRIPTS_URL" >&2
      exit 1
    fi
  fi
  mkdir -p "$(dirname "$GIT_SCRIPTS")"
  # Retry once, in case of a transient network failure.
  git clone --depth 1 -q "$GIT_SCRIPTS_URL" "$GIT_SCRIPTS" \
    || (sleep 1m && git clone --depth 1 -q "$GIT_SCRIPTS_URL" "$GIT_SCRIPTS")
fi

echo "$GIT_SCRIPTS" >&3
