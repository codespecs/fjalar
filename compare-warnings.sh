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

# Exit with status 2 if any command fails, including within a pipeline or a
# function.
set -eE
set -o pipefail
trap 'exit 2' ERR

# The compiler names Fjalar's files relative to valgrind/fjalar, so anchoring
# the pattern at the start of the line excludes fjalar_dwarf.c and Valgrind
# core's m_debuginfo/readelf.c.  Every file in include/ and libiberty/ comes
# from Binutils.  A new Binutils-derived file at the top level of
# valgrind/fjalar must be added both here and in valgrind/fjalar/fjalar.am.
BINUTILS_FILES_RE='(readelf|dwarf|elfcomm|bucomm|demanguse)\.[ch]|include/[^:]*|libiberty/[^:]*'

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

# Print the warnings in build log $1, without line and column numbers.
warnings_without_location() {
  # grep exits with status 1 if there are no warnings, and 2 on error.
  { grep -E "^($files_re):[0-9]+:[0-9]+: warning" "$1" || [ $? -eq 1 ]; } \
    | sed -E 's/:[0-9]+:[0-9]+:/:/' | LC_ALL=C sort
}

# Errors in a process substitution do not affect the script's exit status, so
# use temporary files.
tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT
warnings_without_location "$1" > "$tmpdir/before"
warnings_without_location "$2" > "$tmpdir/after"
status=0
diff "$tmpdir/before" "$tmpdir/after" || status=$?
exit "$status"
