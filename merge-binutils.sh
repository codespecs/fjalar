#!/bin/bash

# This script merges a newer version of Binutils' readelf code into the Fjalar
# tree that contains this script.  See chapter "Updating Readelf from Binutils"
# of doc/valgrind-merge.texinfo.
#
# Usage: ./merge-binutils.sh [--trial] NEWVER [CHERRY-PICK-OPTION...]
#   NEWVER is the Binutils version to merge, such as 2.42.  The old version
#   is BINUTILS_VERSION in valgrind/REVISION.  Each CHERRY-PICK-OPTION, such
#   as -Xpatience, is passed to "git cherry-pick", or with --trial to "git
#   merge-tree", which accepts only strategy options (-X).
#   --trial  Report the size of Fjalar's changes to the old version and the
#            number of conflicts that the merge would have, without changing
#            the work tree, the index, or any ref.  It requires Git 2.40 or
#            later, or 2.43 or later with a CHERRY-PICK-OPTION.  See below.
#
# The script downloads and extracts both versions with download-binutils.sh.
# It creates two commits, which it records as refs refs/binutils-merge/base
# and refs/binutils-merge/new.  Each contains only the files of that Binutils
# version that Fjalar has a copy of, at the paths of Fjalar's copies:  each
# file in BINUTILS_FILES, from Binutils' binutils/ directory, at
# valgrind/fjalar/, and each file under Fjalar's valgrind/fjalar/include/ and
# valgrind/fjalar/libiberty/, from Binutils' include/ and libiberty/.  Then it
# runs "git cherry-pick --no-commit" of refs/binutils-merge/new, which
# merges upstream's changes into Fjalar by a 3-way merge whose base is
# refs/binutils-merge/base.  It uses the diff3 conflict style regardless of
# the user's Git configuration, so each conflict also shows the old
# version's text, which helps in resolving it.  It lists the files with
# conflicts, and exits with status 1 if there are conflicts.  It also lists
# the files that the new version lacks, which the merge deletes.
#
# Before merging, the script writes Fjalar's changes to the old version to
# /tmp/$USER/binutils/OLDVER-NEWVER/binutils-Fjalar.diff.  It is a checklist
# for verifying that the merge kept each of Fjalar's changes, because a merge
# can lose a change without reporting a conflict.
#
# After merging, the script lists the headers that the new version's copies
# of the files include but the old version's do not, directly or through
# another such header, and that Fjalar does not have.  It separately lists
# such headers that are in the new version's release but not in the
# directories that it searches, and such headers that are not in the release,
# such as system headers and headers that building Binutils generates.
#
# With --trial, the script measures how hard the merge would be, for example
# to evaluate a change that reduces Fjalar's differences from Binutils.  It
# measures the Binutils-derived files in the work tree, including
# uncommitted changes to tracked files.  It prints, for each such file that
# Fjalar changed, the number of changes (runs of consecutive changed lines),
# added lines, and removed lines in Fjalar's changes to the old version.
# Then it does the merge in memory, with "git merge-tree", and prints the
# number of conflicts in each file.  It uses the same conflict style and diff
# algorithm as the merge, because they affect how Git splits and combines
# conflicts.  If NEWVER is the old version, it prints only the changes.

set -e
set -o pipefail
# Make a failure inside a command substitution stop the script.
shopt -s inherit_errexit

# Make "cd" with a relative directory resolve it against the current
# directory.
unset CDPATH
# Make sort and comm agree on the sort order.
export LC_ALL=C

trial=false
if [ "${1-}" = --trial ]; then
  trial=true
  shift
fi
if [ $# -lt 1 ]; then
  echo "Usage: $0 [--trial] NEWVER [CHERRY-PICK-OPTION...]" >&2
  exit 2
fi
BUNEWVER=$1
shift
if [ "$trial" = true ]; then
  # "git merge-tree" accepts only the strategy options of "git cherry-pick".
  for option in "$@"; do
    case $option in
      -X?* | --strategy-option=?*) ;;
      *)
        echo "$0: with --trial, each CHERRY-PICK-OPTION must be a strategy option," >&2
        echo "such as -Xpatience, not $option" >&2
        exit 2
        ;;
    esac
  done
  # "git merge-tree" accepts --merge-base since Git 2.40, and -X since 2.43.
  if [ $# -eq 0 ]; then required_git=2.40; else required_git=2.43; fi
  git_version=$(git version | awk '{ print $3 }')
  if [ "$(printf '%s\n' "$required_git" "$git_version" | sort -V | head -n 1)" != "$required_git" ]; then
    echo "$0: --trial${1+ with a CHERRY-PICK-OPTION} requires Git $required_git or later," >&2
    echo "but this is Git $git_version." >&2
    exit 1
  fi
fi

# The Fjalar tree that contains this script, even if $0 is a symbolic link.
FJALARDIR=$(dirname -- "$(readlink -f -- "$0")")
source "$FJALARDIR/binutils-common.sh"
check_version NEWVER "$BUNEWVER"
toplevel=$(git -C "$FJALARDIR" rev-parse --show-toplevel 2> /dev/null) || toplevel=
if [ "$toplevel" != "$FJALARDIR" ]; then
  echo "$0: $FJALARDIR is not the top level of a git clone." >&2
  exit 1
fi
# REVISION is a shell script, so sourcing it handles quoting and comments.
BUOLDVER=$(source "$FJALARDIR/valgrind/REVISION" && printf '%s' "${BINUTILS_VERSION-}")
BUOLDVER=${BUOLDVER%$'\r'}
if [ -z "$BUOLDVER" ]; then
  echo "$0: no BINUTILS_VERSION in $FJALARDIR/valgrind/REVISION" >&2
  echo "Add a line \"export BINUTILS_VERSION=OLDVER\" to that file, where OLDVER" >&2
  echo "is the Binutils version of Fjalar's readelf code, then re-run this script." >&2
  exit 1
fi
check_version "BINUTILS_VERSION in $FJALARDIR/valgrind/REVISION" "$BUOLDVER"
if [ "$BUOLDVER" = "$BUNEWVER" ] && [ "$trial" = false ]; then
  echo "$0: Fjalar's readelf code is already from Binutils $BUNEWVER" >&2
  echo "There is nothing to merge.  To merge a newer version, pass it as NEWVER." >&2
  exit 1
fi
if [ "$(printf '%s\n' "$BUOLDVER" "$BUNEWVER" | sort -V | tail -n 1)" != "$BUNEWVER" ]; then
  echo "$0: NEWVER $BUNEWVER is older than Fjalar's Binutils $BUOLDVER" >&2
  echo "Merging it would undo upstream's changes.  Pass a newer version as NEWVER." >&2
  exit 1
fi

# A clean work tree and index keep the merge separate from other changes, so
# "git reset --hard" can undo it.  A trial changes neither.
changes=$(git -C "$FJALARDIR" status --porcelain --untracked-files=no)
if [ -n "$changes" ] && [ "$trial" = false ]; then
  echo "$0: $FJALARDIR has uncommitted changes:" >&2
  head -n 20 <<< "$changes" >&2
  exit 1
fi

"$FJALARDIR/download-binutils.sh" "$BUOLDVER" "$BUNEWVER"
BUOLD=$BUTMP/binutils-$BUOLDVER
BUNEW=$BUTMP/binutils-$BUNEWVER
OUTDIR=$BUTMP/$BUOLDVER-$BUNEWVER
mkdir -p "$OUTDIR"

cd "$FJALARDIR"

# The files, as paths in a Binutils tree, that Fjalar has a copy of in its
# valgrind/fjalar/ directory.  They come from Binutils directories other than
# include/ and libiberty/, whose files Fjalar's valgrind/fjalar/include/ and
# valgrind/fjalar/libiberty/ have copies of.  When you copy another such file
# into valgrind/fjalar/, add it here, so that later merges merge it.
BINUTILS_FILES="binutils/dwarf.c binutils/dwarf.h binutils/readelf.c binutils/elfcomm.c
  binutils/elfcomm.h binutils/bucomm.h binutils/demanguse.h"

# Usage: fjalar_path PATH
# Prints the path of Fjalar's copy of PATH, a path in a Binutils tree.
fjalar_path() {
  case $1 in
    include/* | libiberty/*) echo "valgrind/fjalar/$1" ;;
    *) echo "valgrind/fjalar/${1##*/}" ;;
  esac
}

# Print each Binutils-derived file of Fjalar, as a line with the path of
# Fjalar's copy, a tab, and the file's path in a Binutils tree.
binutils_paths() {
  local f
  for f in $BINUTILS_FILES; do
    printf '%s\t%s\n' "$(fjalar_path "$f")" "$f"
  done
  git ls-files -- valgrind/fjalar/include valgrind/fjalar/libiberty \
    | sed 's|^valgrind/fjalar/\(.*\)$|&\t\1|'
}
paths=$(binutils_paths)
# The keys are the paths in a Binutils tree of the files that the merge merges.
declare -A merged=()
while IFS=$'\t' read -r _ binutils_path; do
  merged[$binutils_path]=1
done <<< "$paths"

# The temporary directory is in $BUTMP, which no one else can write, and only
# you can read it, so no one else can create or change the index file.
tmpdir=$(mktemp -d "$OUTDIR/tmp.XXXXXX")
tmpindex=$tmpdir/index
# A temporary file in $OUTDIR, so that "mv" can replace the diff atomically.
diff_tmp=$(mktemp "$OUTDIR/binutils-Fjalar.diff.XXXXXX")
trap 'rm -rf "$tmpdir" "$diff_tmp"' EXIT

# Usage: binutils_commit DIR [PARENT]
# Prints the name of a new commit, with parent PARENT if it is given, that
# contains each file of the Binutils tree DIR that Fjalar has a copy of, at
# the path of Fjalar's copy.
binutils_commit() {
  local dir=$1 parent=$2 fjalar_path binutils_path shas i
  local -a fjalar_paths=() files=() modes=()
  while IFS=$'\t' read -r fjalar_path binutils_path; do
    if [ -f "$dir/$binutils_path" ]; then
      fjalar_paths+=("$fjalar_path")
      files+=("$dir/$binutils_path")
      if [ -x "$dir/$binutils_path" ]; then modes+=(100755); else modes+=(100644); fi
    fi
  done <<< "$paths"
  if [ ${#files[@]} -eq 0 ]; then
    echo "$0: $dir has none of the Binutils files that Fjalar has a copy of." >&2
    exit 1
  fi
  shas=$(printf '%s\n' "${files[@]}" | git hash-object -w --no-filters --stdin-paths)
  mapfile -t shas <<< "$shas"
  rm -f "$tmpindex"
  for i in "${!files[@]}"; do
    printf '%s %s\t%s\n' "${modes[i]}" "${shas[i]}" "${fjalar_paths[i]}"
  done | GIT_INDEX_FILE=$tmpindex git update-index --add --index-info
  # The commits are only for the merge, so they need no signature.
  git commit-tree --no-gpg-sign "$(GIT_INDEX_FILE=$tmpindex git write-tree)" \
    ${parent:+-p "$parent"} -m "Binutils ${dir##*/binutils-}"
}

base_commit=$(binutils_commit "$BUOLD")
new_commit=$(binutils_commit "$BUNEW" "$base_commit")

# Usage: fjalar_diff TARGET [ARG...]
# Prints Fjalar's changes to the old version:  the diff from the base commit
# to TARGET, a commit.  Each ARG, such as -U0 or "-- PATH", is passed to "git
# diff" after the commits.  The diff omits the files that are not in the base
# commit, which only Fjalar has.  The options make the output independent of
# the user's Git configuration.  The diff algorithm is the merge's, so that
# the changed lines are the ones that the merge works with, unless a
# CHERRY-PICK-OPTION such as -Xpatience changes the merge's algorithm.
fjalar_diff() {
  git diff --no-renames --no-ext-diff --no-textconv --no-color -U3 \
    --diff-algorithm=histogram --inter-hunk-context=0 \
    --src-prefix=a/ --dst-prefix=b/ --diff-filter=a \
    "$base_commit" "$@"
}

# The options make rename detection and the diff algorithm independent of
# the user's Git configuration.  They are Git's defaults, and a
# CHERRY-PICK-OPTION such as -Xno-renames or -Xpatience overrides them.
# ("git cherry-pick" uses diff.algorithm, but "git merge-tree" does not.)
# The conflict style is fixed so that a trial counts the conflicts that the
# merge has, because the style affects how many conflicts there are.
options=(-c merge.renames=true -c merge.directoryRenames=conflict
  -c diff.algorithm=histogram -c merge.conflictStyle=diff3)

if [ "$trial" = true ]; then
  # A commit of the work tree's tracked files.  A copy of the index records
  # them, so the index is unchanged even if it has unmerged files.
  cp "$(git rev-parse --git-path index)" "$tmpindex"
  GIT_INDEX_FILE=$tmpindex git add --update
  target=$(git commit-tree --no-gpg-sign -p HEAD -m "Fjalar work tree" \
             "$(GIT_INDEX_FILE=$tmpindex git write-tree)")
  echo
  echo "Fjalar's changes to Binutils $BUOLDVER:"
  # Without context lines, each hunk is one change:  a run of consecutive
  # changed lines.  A file's diff may have no hunk, such as one that changes
  # only the mode.
  fjalar_diff "$target" --name-only -z \
    | while IFS= read -r -d '' file; do
        fjalar_diff "$target" -U0 -- "$file" \
          | awk -v file="$file" '
              /^@@/ { in_hunk = 1; changes++; next }
              in_hunk && /^\+/ { added++ }
              in_hunk && /^-/ { removed++ }
              END { printf "%d\t%d\t%d\t%s\n", changes, added, removed, file }'
      done \
    | awk -F'\t' '
        BEGIN { printf "  %7s %6s %8s  %s\n", "changes", "added", "removed", "file" }
        {
          printf "  %7d %6d %8d  %s\n", $1, $2, $3, $4
          changes += $1; added += $2; removed += $3
        }
        END { printf "  %7d %6d %8d  %s\n", changes, added, removed, "total" }'
  if [ "$BUOLDVER" = "$BUNEWVER" ]; then
    exit 0
  fi
  echo
  echo "Conflicts in a merge of Binutils $BUNEWVER:"
  status=0
  merge_output=$(git "${options[@]}" merge-tree --write-tree --name-only --no-messages \
                   --merge-base="$base_commit" "$@" "$target" "$new_commit") || status=$?
  if [ "$status" -gt 1 ]; then
    echo "$0: git merge-tree failed." >&2
    exit 1
  fi
  # The first line is the merged tree; the others are the conflicted files.
  tree=$(head -n 1 <<< "$merge_output")
  conflicted=$(tail -n +2 <<< "$merge_output")
  printf "  %9s  %s\n" "conflicts" "file"
  total=0
  if [ -n "$conflicted" ]; then
    while IFS= read -r file; do
      # A file with a conflict but no conflict markers, such as one that
      # Fjalar changed and the new version deletes, counts as one conflict.
      count=$(git cat-file blob "$tree:$file" 2> /dev/null | grep -c '^<<<<<<< ' || true)
      if [ "$count" -eq 0 ]; then
        count=1
      fi
      printf "  %9d  %s\n" "$count" "$file"
      total=$((total + count))
    done <<< "$conflicted"
  fi
  # A merge can conflict without any file conflicting, as some directory
  # rename conflicts do.  Such a merge counts as one conflict.
  if [ "$status" -eq 1 ] && [ "$total" -eq 0 ]; then
    printf "  %9d  %s\n" 1 "(in no file; the merge reports it)"
    total=1
  fi
  printf "  %9d  %s\n" "$total" "total"
  exit 0
fi

# The refs keep the commits from being garbage-collected, and name them in
# later commands, such as "git diff binutils-merge/base binutils-merge/new".
git update-ref refs/binutils-merge/base "$base_commit"
git update-ref refs/binutils-merge/new "$new_commit"

fjalar_diff HEAD > "$diff_tmp"
chmod "$(printf '%o' $((0666 & ~0$(umask))))" "$diff_tmp"
mv "$diff_tmp" "$OUTDIR/binutils-Fjalar.diff"

status=0
git "${options[@]}" cherry-pick --no-commit "$@" "$new_commit" || status=$?
conflicts=$(git diff --name-only --diff-filter=U)
if [ "$status" -ne 0 ] && [ -z "$conflicts" ]; then
  echo "$0: git cherry-pick failed." >&2
  exit 1
fi
# The files that the new version lacks.  The merge deletes Fjalar's copies,
# or reports a conflict if Fjalar changed a copy.
deleted=$(git diff --no-renames --name-only --diff-filter=D "$base_commit" "$new_commit")

# Usage: includes DIR PATH...
# Prints the names in the #include directives of the files PATH, which are
# paths relative to DIR, one per line.  Each line is a name, a tab, and the
# directory, relative to DIR, of the file that includes it.
includes() {
  local dir=$1
  shift
  if [ $# -eq 0 ]; then
    return
  fi
  (cd "$dir" && awk '
    match($0, /^[[:space:]]*#[[:space:]]*include[[:space:]]*["<][^">]*[">]/) {
      name = substr($0, RSTART, RLENGTH)
      sub(/^[^"<]*["<]/, "", name)
      sub(/[">]$/, "", name)
      dir = FILENAME
      if (!sub(/\/[^\/]*$/, "", dir)) dir = "."
      print name "\t" dir
    }' "$@") | sort -u
}

# Usage: merged_files DIR
# Prints the path, relative to DIR, of each file of the Binutils tree DIR
# that the merge merges.
merged_files() {
  local binutils_path
  for binutils_path in "${!merged[@]}"; do
    if [ -f "$1/$binutils_path" ]; then
      echo "$binutils_path"
    fi
  done
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

# The paths, relative to the new Binutils tree, of the files in its release,
# including those in the directories that download-binutils.sh does not
# extract.
release_files=$(tar tzf "$BUTMP/binutils-$BUNEWVER.tar.gz" | sed 's|^[^/]*/||')

# Usage: release_files_named NAME
# Prints the path, relative to the new Binutils tree, of each file in the
# release whose path ends with NAME.
release_files_named() {
  awk -v name="$1" '$0 == name || substr($0, length($0) - length(name)) == "/" name' \
    <<< "$release_files"
}

# Usage: new_includes
# Copies standard input, lines from "includes", to standard output, except
# for the lines whose name is in $old_includes.
new_includes() {
  awk -F'\t' 'NR == FNR { old[$0]; next } !($1 in old)' \
    <(printf '%s\n' "$old_includes") -
}

# The headers that the new version's files include but the old version's do
# not, directly or through another such header, and that Fjalar does not
# have.  The new version's files include those that Fjalar has, so their
# includes are scanned too.
mapfile -t old_files < <(merged_files "$BUOLD")
mapfile -t new_files < <(merged_files "$BUNEW")
old_includes=$(includes "$BUOLD" "${old_files[@]}" | cut -f1 | sort -u)
# Each pending entry is a header name, a tab, and the directory of the file
# that includes it.
pending=$(includes "$BUNEW" "${new_files[@]}" | new_includes)
declare -A seen=() seen_name=()
missing=
not_in_release=
elsewhere=
while [ -n "$pending" ]; do
  next=
  while IFS=$'\t' read -r name dir; do
    header=$(binutils_header "$name" "$dir")
    if [ -z "$header" ]; then
      if [ -z "${seen_name[$name]}" ]; then
        seen_name[$name]=1
        candidates=$(release_files_named "$name")
        if [ -n "$candidates" ]; then
          elsewhere+="  $name, included from $dir/, may be"$'\n'
          elsewhere+="    ${candidates//$'\n'/$'\n'    }"$'\n'
        else
          not_in_release+="  $name"$'\n'
        fi
      fi
      continue
    fi
    if [ -n "${seen[$header]}" ]; then
      continue
    fi
    seen[$header]=1
    if [ -n "${merged[$header]}" ]; then
      continue
    fi
    missing+="  $BUNEW/$header"$'\n'
    next+=$(includes "$BUNEW" "$header" | new_includes)$'\n'
  done <<< "$pending"
  pending=$(grep -v '^$' <<< "$next" | sort -u || true)
done

echo
if [ -n "$missing" ]; then
  echo "$0: Binutils $BUNEWVER's files include these headers, which Fjalar does not have:"
  echo -n "$missing"
  echo "Copy those that Fjalar needs, or disable the code that includes them."
  echo "Add each copy of a header from outside include/ and libiberty/ to"
  echo "BINUTILS_FILES in $0."
  echo
fi
if [ -n "$elsewhere" ]; then
  echo "$0: Binutils $BUNEWVER's files also include these headers, which are in"
  echo "its release but not in the directories that the script searches.  For"
  echo "each, the script lists the files in the release with that name.  Copy"
  echo "those that Fjalar needs, as described above, or disable the code that"
  echo "includes them:"
  echo -n "$elsewhere"
  echo
fi
if [ -n "$not_in_release" ]; then
  echo "$0: Binutils $BUNEWVER's files also include these headers, which are"
  echo "not in its release.  They may be system headers or headers that building"
  echo "Binutils generates.  Make sure that Fjalar does not need them, or provide"
  echo "what it needs:"
  echo -n "$not_in_release"
  echo
fi
if [ -n "$deleted" ]; then
  echo "$0: Binutils $BUNEWVER lacks these files, so the merge deletes Fjalar's"
  echo "copies of them, or reports a conflict if Fjalar changed them.  Make sure"
  echo "that Fjalar does not use them, and remove any in BINUTILS_FILES from it:"
  echo "  ${deleted//$'\n'/$'\n'  }"
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
