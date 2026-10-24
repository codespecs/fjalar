#!/bin/bash

# This script lists the VEX IR operations (Iop_*) of a Valgrind tree that
# DynComp does not handle.  Running programs finds only the unhandled
# operations that those programs use; this script finds them all.  See
# doc/valgrind-merge.texinfo.
#
# Usage: ./list-dyncomp-missing-iops.sh VALGRIND_DIR
#   VALGRIND_DIR is the Valgrind tree whose operations to check, such as
#   $INV/valgrind-new (the upstream release that is being merged into
#   Fjalar) or this tree's valgrind/ (the current release).
#
# The script reads VALGRIND_DIR/VEX/pub/libvex_ir.h and
# VALGRIND_DIR/memcheck/mc_translate.c, and this tree's
# valgrind/fjalar/kvasir/dyncomp_translate.c.  A file handles an operation
# if the operation is a case label; in dyncomp_translate.c, that includes a
# commented-out case label, which marks an operation that DynComp
# deliberately does not implement.  It prints two lists:
#  * the operations that Memcheck handles but DynComp does not, and
#  * all operations that DynComp does not handle, which are mostly for
#    other architectures.
# Add each relevant one to the appropriate expr2tags_*_DC switch, or add
# it, as a case label, to the comment that lists the operations that DynComp
# does not implement.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

if [ $# -ne 1 ]; then
  echo "Usage: $0 VALGRIND_DIR" >&2
  exit 2
fi
VALGRIND_DIR="$1"

FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"

LIBVEX_IR=$VALGRIND_DIR/VEX/pub/libvex_ir.h
MC_TRANSLATE=$VALGRIND_DIR/memcheck/mc_translate.c
DC_TRANSLATE=$FJALARDIR/valgrind/fjalar/kvasir/dyncomp_translate.c
for f in "$LIBVEX_IR" "$MC_TRANSLATE" "$DC_TRANSLATE"; do
  if [ ! -f "$f" ]; then
    echo "$0: no such file: $f" >&2
    exit 1
  fi
done

# Print C file $1 without its comments.  -fpreprocessed removes comments
# without expanding macros or reading included files.
strip_comments() {
  gcc -fpreprocessed -E -P -x c "$1"
}

# Read operation names on standard input, and print them sorted, without
# duplicates, and without the Iop_INVALID and Iop_LAST markers.
sort_ops() {
  { grep -vxE 'Iop_(INVALID|LAST)' || true; } | LC_ALL=C sort -u
}

# Print the enumerators of the IROp type.
all_ops() {
  strip_comments "$LIBVEX_IR" \
    | sed -n '/\bIop_INVALID\b/,/\bIop_LAST\b/p' \
    | grep -oE '\bIop_[A-Za-z0-9_]+' | sort_ops
}

# Print the Iop_* case labels of C file $1, including commented-out ones.
case_ops() {
  { grep -oE '\bcase[[:space:]]+Iop_[A-Za-z0-9_]+' "$1" || true; } \
    | sed -E 's/^case[[:space:]]+//' | sort_ops
}

echo "Operations that Memcheck handles but DynComp does not:"
LC_ALL=C comm -23 <(case_ops "$MC_TRANSLATE") <(case_ops "$DC_TRANSLATE")
echo
echo "All operations that DynComp does not handle (mostly other architectures):"
LC_ALL=C comm -23 <(all_ops) <(case_ops "$DC_TRANSLATE")
