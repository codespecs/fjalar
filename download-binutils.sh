#!/bin/bash

# This script downloads Binutils releases, for merging a newer version of
# Binutils' readelf code into Fjalar.  See chapter "Updating Readelf from
# Binutils" of doc/valgrind-merge.texinfo.  merge-binutils.sh and
# build-binutils-readelf.sh run it.
#
# Usage: ./download-binutils.sh [--full] VERSION...
#   Each VERSION is a Binutils version, such as 2.42.
#   --full  Extract the whole release, rather than only the directories that
#           Fjalar's copies of Binutils files come from and that they include
#           headers from.  Building Binutils needs the whole release.
#
# The script works in /tmp/$USER/binutils.  For each VERSION, it downloads
# binutils-VERSION.tar.gz, unless it has been downloaded already, verifies its
# signature, and extracts it to /tmp/$USER/binutils/binutils-VERSION/, unless
# that has been done already.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

full=false
if [ "${1-}" = --full ]; then
  full=true
  shift
fi
if [ $# -eq 0 ]; then
  echo "Usage: $0 [--full] VERSION..." >&2
  exit 2
fi
# The Fjalar tree that contains this script, even if $0 is a symbolic link.
FJALARDIR=$(dirname -- "$(readlink -f -- "$0")")
source "$FJALARDIR/binutils-common.sh"
for version in "$@"; do
  check_version VERSION "$version"
done

# Another user could plant a Binutils tree, whose configure script
# build-binutils-readelf.sh runs, in a directory that they own or can write.
# The umask keeps a directory that mkdir creates from being writable by others.
# A symbolic link is rejected because "-O" and "find" check its target, which
# need not be the directory that later commands use.  A directory that is not
# a symbolic link and that only you own and can write cannot be replaced by
# anyone else, given that /tmp is sticky, so the check need not be repeated.
(umask 077 && mkdir -p "$BUTMP")
for dir in "/tmp/$USER" "$BUTMP"; do
  if [ -L "$dir" ] || [ ! -d "$dir" ] || [ ! -O "$dir" ] \
       || [ -n "$(find "$dir" -maxdepth 0 -perm /022)" ]; then
    echo "$0: $dir must be a directory, not a symbolic link," >&2
    echo "that is owned by you and writable by no one else." >&2
    echo "Delete it or fix its ownership and permissions, then re-run this script." >&2
    exit 1
  fi
done
cd "$BUTMP"

# Usage: download URL
# Downloads URL into the current directory, unless the file exists already.
# It downloads to a temporary name, so that an interrupted download leaves no
# partial file that a later run would reuse.
download() {
  local file
  file=$(basename "$1")
  if [ ! -f "$file" ]; then
    wget -nv -O "$file.part" "$1"
    mv "$file.part" "$file"
  fi
}

# gpgv checks the signatures against the GNU keyring, rather than against the
# user's own keyring, which may lack the signers' keys.
download https://ftp.gnu.org/gnu/gnu-keyring.gpg
for version in "$@"; do
  f=binutils-$version
  download https://ftp.gnu.org/gnu/binutils/"$f.tar.gz"
  download https://ftp.gnu.org/gnu/binutils/"$f.tar.gz.sig"
  if ! gpgv --keyring "$BUTMP/gnu-keyring.gpg" "$f.tar.gz.sig" "$f.tar.gz"; then
    echo "$0: the signature of $BUTMP/$f.tar.gz is not valid" >&2
    echo "The download may be corrupt, or the keyring may lack a newer signer's key." >&2
    echo "Delete $BUTMP/$f.tar.gz, $BUTMP/$f.tar.gz.sig, and" >&2
    echo "$BUTMP/gnu-keyring.gpg, so that they are downloaded again, then re-run" >&2
    echo "this script.  If the signature is still not valid, do not use the file." >&2
    exit 1
  fi
  # A whole release is much larger than the directories that a merge needs,
  # and /tmp may be small.  A tree that an earlier run extracted only partly,
  # such as because it was interrupted, is not reused.
  if [ "$full" = true ]; then
    if [ ! -f "$f/.extracted-full" ]; then
      rm -rf "$f"
      tar xzf "$f.tar.gz"
      touch "$f/.extracted" "$f/.extracted-full"
    fi
  elif [ ! -f "$f/.extracted" ]; then
    rm -rf "$f"
    tar xzf "$f.tar.gz" "$f/binutils" "$f/include" "$f/libiberty" "$f/bfd"
    touch "$f/.extracted"
  fi
done
