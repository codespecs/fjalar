#!/bin/bash

# This script creates patch files that are used when merging a newer
# version of upstream Valgrind into Fjalar and Kvasir.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

# Make "cd" with a relative directory resolve it against the current
# directory, as "git -C" does.
unset CDPATH

if [ -z "$INV" ]; then
  echo "$0: INV is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi

# Remove all the output files first, so that a failure, including a failed
# check below, does not leave stale ones from an earlier run.
rm -f "$INV"/{coregrind.patch,memcheck.patch,coregrind-Fjalar.diff,memcheck-Fjalar.diff}

for dir in "$INV/valgrind-old" "$INV/valgrind-new" "$INV/fjalar/valgrind"; do
  if [ ! -d "$dir" ]; then
    echo "$0: $dir does not exist." >&2
    exit 1
  fi
done

# Any build product in an upstream tree would end up in coregrind.patch,
# and applying the patch would copy it into Fjalar.  So both trees must be
# pristine clones.  Build the upstream baseline in a copy instead.
for dir in "$INV/valgrind-old" "$INV/valgrind-new"; do
  # Without this check, "git status" would report on an enclosing
  # repository, or would fail and produce no output.
  toplevel=$(git -C "$dir" rev-parse --show-toplevel 2> /dev/null) || toplevel=
  if [ "$toplevel" != "$(cd -- "$dir" > /dev/null && pwd -P)" ]; then
    echo "$0: $dir is not the top level of a git clone." >&2
    exit 1
  fi
  status=$(git -C "$dir" status --porcelain --ignored)
  if [ -n "$status" ]; then
    echo "$0: $dir has changes or files that are not in its git" >&2
    echo "$0: repository, such as build products.  It must be a pristine clone:" >&2
    head -n 20 <<< "$status" >&2
    count=$(wc -l <<< "$status")
    if [ "$count" -gt 20 ]; then
      echo "$0: ... and $((count - 20)) more." >&2
    fi
    echo "$0: To discard changes and remove untracked files and build products, run:" >&2
    echo "$0:   git -C \"$dir\" reset --hard && git -C \"$dir\" clean -fdx" >&2
    exit 1
  fi
done

# At the next merge, it is easy to forget to move valgrind-new to
# valgrind-old, or to clone the wrong tag.
# Usage: check_version DIR VARNAME
# If variable VARNAME is set, checks that DIR is at the tag it names.
check_version() {
  local dir=$1 var=$2
  local ver=${!var}
  local commit
  if [ -z "$ver" ]; then
    return
  fi
  if ! commit=$(git -C "$dir" rev-parse --verify -q "refs/tags/$ver^{commit}"); then
    echo "$0: $dir has no tag $ver (the value of $var)." >&2
    exit 1
  fi
  if [ "$(git -C "$dir" rev-parse HEAD)" != "$commit" ]; then
    echo "$0: $dir is not at tag $ver (the value of $var)." >&2
    exit 1
  fi
}
check_version "$INV/valgrind-old" VOLDVER
check_version "$INV/valgrind-new" VNEWVER

cd "$INV"
inv=$(pwd -P)

# The temporary file that run_diff is writing, if any, and the copy of
# fjalar/valgrind.  They are removed when the script exits, including when
# it exits early or is interrupted.
tmp=
fjalar_copy=
trap 'rm -f "$tmp"; [ -z "$fjalar_copy" ] || rm -rf "$fjalar_copy"' EXIT

# Usage: run_diff OUTFILE DIFF-ARGS...
# Creates OUTFILE only if diff succeeds, so a failure does not leave a
# partial file.  diff exits with status 1 if the files differ, which is
# expected, and with status 2 if there was trouble.
run_diff() {
  local out=$1
  shift
  tmp=$out.tmp
  # Create the file before running diff.  A failed redirection on the diff
  # command would yield status 1, which is indistinguishable from "files differ".
  if ! : > "$tmp"; then
    echo "$0: cannot write $tmp, so $out was not created." >&2
    exit 1
  fi
  if diff "$@" >> "$tmp" || [ $? -eq 1 ]; then
    mv "$tmp" "$out"
    tmp=
  else
    echo "$0: diff failed, so $out was not created." >&2
    exit 1
  fi
}

run_diff coregrind.patch -ur --unidirectional-new-file -x.git valgrind-old valgrind-new
# generate-fjalar-makefile.sh generates Fjalar's version of
# memcheck/Makefile.am, so memcheck.patch omits it.
run_diff memcheck.patch -ur --unidirectional-new-file -x.git -xdocs -xtests -xMakefile.am valgrind-old/memcheck valgrind-new/memcheck

# fjalar/valgrind is usually built in place.  To keep build products out of
# the Fjalar diffs, diff a copy of the files that git does not ignore.  The
# copy is in a directory that mirrors $INV, so the diffs show the same
# paths as if they had been run in $INV.
fjalar_copy=$(mktemp -d)
ln -s "$inv/valgrind-old" "$fjalar_copy/valgrind-old"
mkdir "$fjalar_copy/fjalar"
# Omit tracked files that have been deleted from the work tree.  Any other
# failure to read a file stops the script, rather than producing an
# incomplete diff.
git -C fjalar ls-files -z --cached --others --exclude-standard -- valgrind \
  | (cd fjalar \
     && while IFS= read -r -d '' f; do
          if [ -e "$f" ] || [ -L "$f" ]; then printf '%s\0' "$f"; fi
        done) \
  | tar -C fjalar --null --files-from=- -cf - \
  | tar -C "$fjalar_copy/fjalar" -xf -
cd "$fjalar_copy"
run_diff "$inv/coregrind-Fjalar.diff" -ur -x.git -xfjalar valgrind-old fjalar/valgrind
run_diff "$inv/memcheck-Fjalar.diff" -ur -x.git -xhtml -xdocs -xtests valgrind-old/memcheck fjalar/valgrind/fjalar
