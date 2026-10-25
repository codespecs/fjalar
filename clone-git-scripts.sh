#!/bin/bash

# Clones or updates https://github.com/plume-lib/git-scripts, then prints the
# directory that contains it.
#
# Usage:  GIT_SCRIPTS="$(clone-git-scripts.sh [DIRECTORY])"
#
# The directory is the argument if one is given and non-empty, otherwise
# $GIT_SCRIPTS if it is set and non-empty, otherwise /tmp/USERNAME/git-scripts.
# USERNAME is $USER if it is set and non-empty, otherwise `id -un`.
# The directory, and for the default the /tmp/USERNAME directory, must be owned
# by the current user and not be group- or world-writable; otherwise another
# user could substitute the scripts that the caller runs.

# Fail the whole script if any command fails.
set -e

# Standard output is the return value, so send everything else to standard error.
exec 3>&1 1>&2

if [ "$#" -gt 1 ] ; then
  echo "Usage: $0 [DIRECTORY]" >&2
  exit 2
fi

# Do not make a new clone writable by other users.
umask 022

# Exits with an error if the argument exists but is not owned by the current
# user or is group- or world-writable.
require_private() {
  if [ -e "$1" ] ; then
    perms="$(ls -ldL "$1")"
    if [ ! -O "$1" ] || [ "${perms:5:1}" = w ] || [ "${perms:8:1}" = w ] ; then
      echo "$0: $1 must be owned by $(id -un) and not be group- or world-writable." >&2
      echo "If you trust its contents, run:  chmod go-w $1" >&2
      exit 1
    fi
  fi
}

if [ -n "${1:-}" ] ; then
  GIT_SCRIPTS="$1"
elif [ -z "${GIT_SCRIPTS:-}" ] ; then
  PRIVATE_TMPDIR="/tmp/${USER:-$(id -un)}"
  # Another user can replace a symbolic link in /tmp, so do not follow one.
  if [ -L "$PRIVATE_TMPDIR" ] ; then
    echo "$0: $PRIVATE_TMPDIR is a symbolic link" >&2
    exit 1
  elif [ ! -e "$PRIVATE_TMPDIR" ] ; then
    mkdir -m 700 "$PRIVATE_TMPDIR"
  fi
  require_private "$PRIVATE_TMPDIR"
  GIT_SCRIPTS="$PRIVATE_TMPDIR/git-scripts"
fi
require_private "$GIT_SCRIPTS"
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
