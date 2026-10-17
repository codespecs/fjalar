#!/bin/bash

# This script creates patch files that are used when merging a newer
# version of upstream Valgrind into Fjalar and Kvasir.

# Fail the whole script if any command fails.
set -e

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
# and then be added to Fjalar by "make git-update".  So both trees must be
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
    echo "$status" | head -n 20 >&2
    echo "$0: To discard changes and remove untracked files and build products, run:" >&2
    echo "$0:   git -C \"$dir\" reset --hard && git -C \"$dir\" clean -fdx" >&2
    exit 1
  fi
done

cd "$INV"

# The temporary file that run_diff is writing, if any.  It is removed if
# the script exits early, including when it is interrupted.
tmp=
trap 'rm -f "$tmp"' EXIT

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
run_diff memcheck.patch -ur --unidirectional-new-file -x.git -xdocs -xtests valgrind-old/memcheck valgrind-new/memcheck
run_diff coregrind-Fjalar.diff -ur -xinst -x.git -xfjalar -xMakefile.in valgrind-old fjalar/valgrind
run_diff memcheck-Fjalar.diff -ur -xinst -x.git -xMakefile.in -xhtml -xdocs -xtests valgrind-old/memcheck fjalar/valgrind/fjalar
