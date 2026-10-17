#!/bin/bash

# This script creates patch files that are used when merging a newer
# version of upstream Valgrind into Fjalar and Kvasir.

# Fail the whole script if any command fails.
set -e

if [ -z "$INV" ]; then
  echo "$0: INV is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi
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
  if [ -n "$(git -C "$dir" status --porcelain --ignored)" ]; then
    echo "$0: $dir has changes or files that are not in its git" >&2
    echo "repository, such as build products.  It must be a pristine clone:" >&2
    git -C "$dir" status --porcelain --ignored | head -n 20 >&2
    exit 1
  fi
done

cd "$INV"

# diff exits with status 1 if the files differ, which is expected, and with
# status 2 if there was trouble.
run_diff() {
  diff "$@" || [ $? -eq 1 ]
}

rm -f coregrind.patch
run_diff -ur --unidirectional-new-file -x.git valgrind-old valgrind-new > coregrind.patch

rm -f  memcheck.patch
run_diff -ur --unidirectional-new-file -x.git -xdocs -xtests valgrind-old/memcheck valgrind-new/memcheck > memcheck.patch

rm -f coregrind-Fjalar.diff
run_diff -ur -xinst -x.git -xfjalar -xMakefile.in -xfjalar/html valgrind-old fjalar/valgrind > coregrind-Fjalar.diff

rm -f memcheck-Fjalar.diff
run_diff -ur -xinst -x.git -xMakefile.in -xhtml -xdocs -xtests valgrind-old/memcheck fjalar/valgrind/fjalar > memcheck-Fjalar.diff
