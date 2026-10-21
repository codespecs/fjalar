# shellcheck shell=bash

# This file defines what merge-binutils.sh, download-binutils.sh, and
# build-binutils-readelf.sh have in common.  Each of them sources it.

# The directory in which the scripts download, extract, and build Binutils.
# shellcheck disable=SC2034 # The scripts that source this file use it.
BUTMP=/tmp/$USER/binutils

# Usage: check_version WHAT VERSION
# Exits with status 2, after printing a message that calls VERSION WHAT,
# unless VERSION is a version number such as 2.42.
check_version() {
  if ! [[ "$2" =~ ^[0-9]+(\.[0-9]+)+$ ]]; then
    echo "$0: $1 must be a version number such as 2.42, not \"$2\"" >&2
    exit 2
  fi
}
