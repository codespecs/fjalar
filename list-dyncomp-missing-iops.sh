#!/bin/bash

# This script lists the VEX IR operations (Iop_*) of the upstream Valgrind
# release that is being merged into Fjalar that DynComp does not mention.
# Running programs finds only the unhandled operations that those programs
# use; this script finds them all.  See doc/valgrind-merge.texinfo.
#
# Usage: ./list-dyncomp-missing-iops.sh
#
# The script reads $INV/valgrind-new/VEX/pub/libvex_ir.h and
# $INV/valgrind-new/memcheck/mc_translate.c, and this tree's
# valgrind/fjalar/kvasir/dyncomp_translate.c.  It prints two lists:
#  * the operations that Memcheck handles but DynComp does not mention, and
#  * all operations that DynComp does not mention, which are mostly for
#    other architectures.
# Add each relevant one to the appropriate expr2tags_*_DC switch, or leave
# it to the default case deliberately, with a comment.

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

if [ $# -ne 0 ]; then
  echo "Usage: $0" >&2
  exit 2
fi

FJALARDIR="$(cd "$(dirname "$0")" && pwd -P)"

if [ -z "$INV" ]; then
  echo "$0: INV is not set; see doc/valgrind-merge.texinfo." >&2
  exit 1
fi
LIBVEX_IR=$INV/valgrind-new/VEX/pub/libvex_ir.h
MC_TRANSLATE=$INV/valgrind-new/memcheck/mc_translate.c
DC_TRANSLATE=$FJALARDIR/valgrind/fjalar/kvasir/dyncomp_translate.c
for f in "$LIBVEX_IR" "$MC_TRANSLATE" "$DC_TRANSLATE"; do
  if [ ! -f "$f" ]; then
    echo "$0: no such file: $f" >&2
    exit 1
  fi
done

# Print the Iop_* names that file $1 mentions, sorted and without duplicates.
ops() {
  { grep -oE '\bIop_[A-Za-z0-9_]+' "$1" || true; } | LC_ALL=C sort -u
}

echo "Operations that Memcheck handles but DynComp does not mention:"
LC_ALL=C comm -23 <(ops "$MC_TRANSLATE") <(ops "$DC_TRANSLATE")
echo
echo "All operations that DynComp does not mention (mostly other architectures):"
LC_ALL=C comm -23 <(ops "$LIBVEX_IR") <(ops "$DC_TRANSLATE")
