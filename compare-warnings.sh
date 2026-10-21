#!/bin/bash

# This script lists the compiler warnings that are new in a build log, by
# comparing it with the log of an earlier build.  It is for merges of
# Valgrind and of Binutils' readelf code into Fjalar; see
# doc/valgrind-merge.texinfo.
#
# Usage: ./compare-warnings.sh [--binutils] BEFORE.log AFTER.log
#   --binutils  Compare only the warnings for the Binutils-derived files in
#               valgrind/fjalar/.
#
# A merge shifts line numbers, so the script removes the line and column
# numbers from the warnings before comparing them.  It prints the output of
# "diff" on the two sorted lists of warnings:  "<" lines are warnings that
# only BEFORE.log has, and ">" lines are new warnings.  An incremental build
# prints no warnings for the files that it does not recompile, so both logs
# should be from builds that compiled every file of interest.
#
# Exit status: 0 if the warnings are the same, 1 if they differ, 2 on error.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

# The compiler names Fjalar's files relative to valgrind/fjalar, so anchoring
# the pattern at the start of the line excludes fjalar_dwarf.c and Valgrind
# core's m_debuginfo/readelf.c.
BINUTILS_FILES_RE='(readelf|dwarf|elfcomm|bucomm|demanguse)\.[ch]|include/[^:]*\.h|libiberty/dwarfnames\.c'

files_re='[^:]+'
if [ "${1-}" = --binutils ]; then
  files_re=$BINUTILS_FILES_RE
  shift
fi
if [ $# -ne 2 ]; then
  echo "Usage: $0 [--binutils] BEFORE.log AFTER.log" >&2
  exit 2
fi
for f in "$1" "$2"; do
  if [ ! -f "$f" ]; then
    echo "$0: no such file: $f" >&2
    exit 2
  fi
done

tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

# Print the warnings in build log $1, without line and column numbers.
warnings_without_location() {
  # grep exits with status 1 if the log has no warnings, and with status 2
  # if it cannot read the log.
  { grep -E "^($files_re):[0-9]+:[0-9]+: warning" "$1" || [ $? -eq 1 ]; } \
    | sed -E 's/:[0-9]+:[0-9]+:/:/' | LC_ALL=C sort
}

# The lists are written to files, rather than passed to diff by process
# substitution, so that a failure to read a log stops the script.
if ! warnings_without_location "$1" > "$tmpdir/before" \
    || ! warnings_without_location "$2" > "$tmpdir/after"; then
  echo "$0: cannot read the build logs" >&2
  exit 2
fi
diff "$tmpdir/before" "$tmpdir/after"
