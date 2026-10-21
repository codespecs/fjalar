#!/bin/bash

# This script merges a newer version of Binutils' readelf code into the Fjalar
# tree that contains this script.  See chapter "Updating Readelf from Binutils"
# of doc/valgrind-merge.texinfo.
#
# Usage: ./merge-binutils.sh NEWVER [CHERRY-PICK-OPTION...]
#   NEWVER is the Binutils version to merge, such as 2.42.  The old version
#   is BINUTILS_VERSION in valgrind/REVISION.  Each CHERRY-PICK-OPTION, such
#   as -Xpatience, is passed to "git cherry-pick".
#
# The script downloads and extracts both versions with download-binutils.sh.
# It creates two commits, which it records as refs refs/binutils-merge/base
# and refs/binutils-merge/new.  Each contains only the files of that Binutils
# version that Fjalar has a copy of, at the paths of Fjalar's copies:  each
# file in BINUTILS_FILES, from Binutils' binutils/ directory, at
# valgrind/fjalar/, and each file under Fjalar's valgrind/fjalar/include/ and
# valgrind/fjalar/libiberty/, from Binutils' include/ and libiberty/.  The
# script also records Fjalar's HEAD as ref refs/binutils-merge/fjalar.  Then
# it runs "git cherry-pick --no-commit" of refs/binutils-merge/new, which
# merges upstream's changes into Fjalar by a 3-way merge whose base is
# refs/binutils-merge/base.  It lists the files with conflicts, and exits
# with status 1 if there are conflicts.
#
# Before merging, the script writes Fjalar's changes to the old version to
# /tmp/$USER/binutils/OLDVER-NEWVER/binutils-Fjalar.diff.  It is a checklist
# for verifying that the merge kept each of Fjalar's changes, because a merge
# can lose a change without reporting a conflict.
#
# After merging, the script lists the headers that the new version's copies
# of the files include but the old version's do not, directly or through
# another such header, and that Fjalar does not have.

set -e
set -o pipefail
# Make a failure inside a command substitution stop the script.
shopt -s inherit_errexit

# Make "cd" with a relative directory resolve it against the current
# directory.
unset CDPATH
# Make sort and comm agree on the sort order.
export LC_ALL=C

if [ $# -lt 1 ]; then
  echo "Usage: $0 NEWVER [CHERRY-PICK-OPTION...]" >&2
  exit 2
fi
BUNEWVER=$1
shift
if ! [[ "$BUNEWVER" =~ ^[0-9]+(\.[0-9]+)+$ ]]; then
  echo "$0: NEWVER must be a version number such as 2.42, not $BUNEWVER" >&2
  exit 2
fi

# The Fjalar tree that contains this script, even if $0 is a symbolic link.
FJALARDIR=$(dirname -- "$(readlink -f -- "$0")")
toplevel=$(git -C "$FJALARDIR" rev-parse --show-toplevel 2> /dev/null) || toplevel=
if [ "$toplevel" != "$FJALARDIR" ]; then
  echo "$0: $FJALARDIR is not the top level of a git clone." >&2
  exit 1
fi
BUOLDVER=$(sed -n 's/^export BINUTILS_VERSION=//p' "$FJALARDIR/valgrind/REVISION")
if [ -z "$BUOLDVER" ]; then
  echo "$0: no BINUTILS_VERSION in $FJALARDIR/valgrind/REVISION" >&2
  echo "Add a line \"export BINUTILS_VERSION=OLDVER\" to that file, where OLDVER" >&2
  echo "is the Binutils version of Fjalar's readelf code, then re-run this script." >&2
  exit 1
fi
if [ "$BUOLDVER" = "$BUNEWVER" ]; then
  echo "$0: Fjalar's readelf code is already from Binutils $BUNEWVER" >&2
  echo "There is nothing to merge.  To merge a newer version, pass it as NEWVER." >&2
  exit 1
fi

# A clean work tree and index keep the merge separate from other changes, so
# "git reset --hard" can undo it.
changes=$(git -C "$FJALARDIR" status --porcelain --untracked-files=no)
if [ -n "$changes" ]; then
  echo "$0: $FJALARDIR has uncommitted changes:" >&2
  head -n 20 <<< "$changes" >&2
  exit 1
fi

"$FJALARDIR/download-binutils.sh" "$BUOLDVER" "$BUNEWVER"
BUTMP=/tmp/$USER/binutils
BUOLD=$BUTMP/binutils-$BUOLDVER
BUNEW=$BUTMP/binutils-$BUNEWVER
OUTDIR=$BUTMP/$BUOLDVER-$BUNEWVER
mkdir -p "$OUTDIR"

cd "$FJALARDIR"

# The files in Fjalar's valgrind/fjalar/ directory that are copies of files in
# Binutils' binutils/ directory.
BINUTILS_FILES="dwarf.c dwarf.h readelf.c elfcomm.c elfcomm.h bucomm.h demanguse.h"

# Print each Binutils-derived file of Fjalar, as a line with the path of
# Fjalar's copy, a tab, and the file's path in a Binutils tree.
binutils_paths() {
  local f
  for f in $BINUTILS_FILES; do
    printf 'valgrind/fjalar/%s\tbinutils/%s\n' "$f" "$f"
  done
  git ls-files -- valgrind/fjalar/include valgrind/fjalar/libiberty \
    | sed 's|^valgrind/fjalar/\(.*\)$|&\t\1|'
}
paths=$(binutils_paths)

tmpindex=$(mktemp)
# A temporary file in $OUTDIR, so that "mv" can replace the diff atomically.
diff_tmp=$(mktemp "$OUTDIR/binutils-Fjalar.diff.XXXXXX")
trap 'rm -f "$tmpindex" "$diff_tmp"' EXIT

# Usage: binutils_commit DIR [PARENT]
# Prints the name of a new commit, with parent PARENT if it is given, that
# contains each file of the Binutils tree DIR that Fjalar has a copy of, at
# the path of Fjalar's copy.
binutils_commit() {
  local dir=$1 parent=$2 fjalar_path binutils_path mode sha
  rm -f "$tmpindex"
  while IFS=$'\t' read -r fjalar_path binutils_path; do
    if [ -f "$dir/$binutils_path" ]; then
      if [ -x "$dir/$binutils_path" ]; then mode=100755; else mode=100644; fi
      sha=$(git hash-object -w --no-filters -- "$dir/$binutils_path")
      printf '%s %s\t%s\n' "$mode" "$sha" "$fjalar_path"
    fi
  done <<< "$paths" | GIT_INDEX_FILE=$tmpindex git update-index --add --index-info
  # The commits are only for the merge, so they need no signature.
  git commit-tree --no-gpg-sign "$(GIT_INDEX_FILE=$tmpindex git write-tree)" \
    ${parent:+-p "$parent"} -m "Binutils ${dir##*/binutils-}"
}

base_commit=$(binutils_commit "$BUOLD")
new_commit=$(binutils_commit "$BUNEW" "$base_commit")
# The refs keep the commits from being garbage-collected, and name them in
# later commands, such as "git diff binutils-merge/base binutils-merge/new".
git update-ref refs/binutils-merge/base "$base_commit"
git update-ref refs/binutils-merge/new "$new_commit"
git update-ref refs/binutils-merge/fjalar HEAD

# The options make the output independent of the user's Git configuration.
# The diff omits the files that are not in the base commit, which only Fjalar
# has.
git diff --no-renames --no-ext-diff --no-textconv --no-color -U3 --diff-filter=a \
  "$base_commit" HEAD > "$diff_tmp"
chmod "$(printf '%o' $((0666 & ~0$(umask))))" "$diff_tmp"
mv "$diff_tmp" "$OUTDIR/binutils-Fjalar.diff"

# The options make rename detection independent of the user's Git
# configuration.  They are Git's defaults, and a CHERRY-PICK-OPTION such as
# -Xno-renames overrides them.  Unless the user has chosen a conflict style,
# each conflict also shows the old version's text, which helps in resolving
# it.
options=(-c merge.renames=true -c merge.directoryRenames=conflict)
if ! git config --get merge.conflictStyle > /dev/null; then
  options+=(-c merge.conflictStyle=diff3)
fi
status=0
git "${options[@]}" cherry-pick --no-commit "$@" "$new_commit" || status=$?
conflicts=$(git diff --name-only --diff-filter=U)
if [ "$status" -ne 0 ] && [ -z "$conflicts" ]; then
  echo "$0: git cherry-pick failed." >&2
  exit 1
fi

# Usage: includes FILE...
# Prints the names in the #include directives of the FILEs, one per line.
includes() {
  sed -n 's/^[[:space:]]*#[[:space:]]*include[[:space:]]*["<]\([^">]*\)[">].*/\1/p' "$@" \
    | sort -u
}

# Usage: binutils_header NAME DIR
# Prints the path, relative to the new Binutils tree, of the header that an
# #include of NAME in a file in directory DIR of that tree refers to, if it
# exists there.
binutils_header() {
  local name=$1 dir
  for dir in "$2" binutils include bfd libiberty; do
    if [ -f "$BUNEW/$dir/$name" ]; then
      realpath -m --relative-to="$BUNEW" "$BUNEW/$dir/$name"
      return
    fi
  done
}

# Usage: fjalar_has HEADER
# Succeeds if Fjalar has a copy of HEADER, a path relative to a Binutils tree.
fjalar_has() {
  case $1 in
    binutils/*) [ -f "valgrind/fjalar/${1#binutils/}" ] ;;
    include/* | libiberty/*) [ -f "valgrind/fjalar/$1" ] ;;
    *) [ -f "valgrind/fjalar/$(basename "$1")" ] || [ -f "valgrind/fjalar/include/$(basename "$1")" ] ;;
  esac
}

# The headers that the new version's files include but the old version's do
# not, directly or through another such header, and that Fjalar does not have.
old_files=() new_files=()
for f in $BINUTILS_FILES; do
  if [ -f "$BUOLD/binutils/$f" ]; then old_files+=("$BUOLD/binutils/$f"); fi
  if [ -f "$BUNEW/binutils/$f" ]; then new_files+=("$BUNEW/binutils/$f"); fi
done
old_includes=$(includes "${old_files[@]}")
# Each pending entry is a header name, a tab, and the directory of the file
# that includes it.
pending=$(comm -13 <(echo "$old_includes") <(includes "${new_files[@]}") | sed 's/$/\tbinutils/')
declare -A seen=()
missing=
while [ -n "$pending" ]; do
  next=
  while IFS=$'\t' read -r name dir; do
    header=$(binutils_header "$name" "$dir")
    if [ -z "$header" ] || [ -n "${seen[$header]}" ]; then
      continue
    fi
    seen[$header]=1
    if fjalar_has "$header"; then
      continue
    fi
    missing+="  $BUNEW/$header"$'\n'
    next+=$(includes "$BUNEW/$header" | { grep -vxF -- "$old_includes" || true; } \
              | sed "s|\$|\t$(dirname "$header")|")$'\n'
  done <<< "$pending"
  pending=$(grep -v '^$' <<< "$next" || true)
done

echo
if [ -n "$missing" ]; then
  echo "$0: Binutils $BUNEWVER's files include these headers, which Fjalar does not have:"
  echo -n "$missing"
  echo "Copy those that Fjalar needs, or disable the code that includes them."
  echo
fi
echo "The checklist of Fjalar's changes to Binutils $BUOLDVER is"
echo "  $OUTDIR/binutils-Fjalar.diff"
echo "To undo the merge:  git -C $(printf %q "$FJALARDIR") reset --hard"
echo "After the merge, set BINUTILS_VERSION=$BUNEWVER in"
echo "$(printf %q "$FJALARDIR/valgrind/REVISION")."
if [ -n "$conflicts" ]; then
  echo
  echo "$0: Resolve the conflicts in these files:"
  echo "$conflicts"
  exit 1
fi
echo "$0: merged without conflicts; the changes are staged."
