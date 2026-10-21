# shellcheck shell=bash

# This file defines what merge-binutils.sh, download-binutils.sh, and
# build-binutils-readelf.sh have in common.  Each of them sources it.

# The directory in which the scripts download, extract, and build Binutils.
BUTMP=/tmp/$USER/binutils

# Usage: make_butmp
# Creates $BUTMP if it does not exist, and exits with status 1, after printing
# a message, unless $BUTMP and its parent are safe to use.
# Another user could plant a Binutils tree, whose configure script
# build-binutils-readelf.sh runs, or a readelf program, in a directory that
# they own or can write.  The umask keeps a directory that mkdir creates from
# being writable by others.  A symbolic link is rejected because "-O" and
# "find" check its target, which need not be the directory that later
# commands use.  A directory that is not a symbolic link and that only you
# own and can write cannot be replaced by anyone else, given that /tmp is
# sticky, so the check need not be repeated.  A group-writable directory is
# rejected even if you are the only member of its group, because checking
# the group's members is not reliable.
make_butmp() {
  local dir
  (umask 077 && mkdir -p "$BUTMP")
  for dir in "/tmp/$USER" "$BUTMP"; do
    if [ -L "$dir" ] || [ ! -d "$dir" ] || [ ! -O "$dir" ]; then
      echo "$0: $dir must be a directory, not a symbolic link," >&2
      echo "that is owned by you and writable by no one else." >&2
      echo "Delete it, then re-run this script." >&2
      exit 1
    fi
    if [ -n "$(find "$dir" -maxdepth 0 -perm /022)" ]; then
      echo "$0: $dir must be writable by no one but you." >&2
      echo "If no one else has written to it, make it so and re-run this script:" >&2
      echo "  chmod go-w $(printf %q "$dir")" >&2
      echo "Otherwise, delete it, then re-run this script." >&2
      exit 1
    fi
  done
}

# Usage: check_version WHAT VERSION
# Exits with status 2, after printing a message that calls VERSION WHAT,
# unless VERSION is a version number such as 2.42.
check_version() {
  if ! [[ "$2" =~ ^[0-9]+(\.[0-9]+)+$ ]]; then
    echo "$0: $1 must be a version number such as 2.42, not \"$2\"" >&2
    exit 2
  fi
}
