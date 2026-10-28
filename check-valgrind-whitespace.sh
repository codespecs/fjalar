#!/bin/bash

# This script checks that Fjalar's copies of upstream Valgrind files have
# upstream's whitespace:  that diff-from-valgrind.sh reports the same changes
# when it ignores whitespace and blank lines as when it does not.  A change of
# whitespace alone serves no purpose, but it is a potential conflict in the next
# Valgrind merge.  An editor that removes trailing whitespace when it saves a
# file makes such changes; see .editorconfig.
#
# Usage: check-valgrind-whitespace.sh [--valgrind=DIR]
#   DIR is as for diff-from-valgrind.sh.
#
# The script exits with status 1, after listing the files that have
# whitespace changes, if there are any.

set -e
set -o pipefail
# Make a failure inside a command substitution stop the script.
shopt -s inherit_errexit

# Make sort and join agree on the order of file names.
export LC_ALL=C

if [ $# -gt 1 ] || { [ $# -eq 1 ] && [[ "$1" != --valgrind=* ]]; }; then
  echo "Usage: $0 [--valgrind=DIR]" >&2
  exit 2
fi

# The Fjalar tree that contains this script, even if $0 is a symbolic link.
fjalar=$(dirname -- "$(readlink -f -- "$0")")

# Each line is the number of added lines, the number of removed lines, and
# the file name.  Ignoring whitespace removes a file whose changes are all
# whitespace, and lowers the numbers of a file that has some.  -w does not
# ignore an added or removed blank line, but --ignore-blank-lines does.
# The numbers do not reveal a whitespace change to a line that also moved,
# because the diff does not pair the line with its upstream version, but the
# move alone is a potential conflict.
plain=$("$fjalar/diff-from-valgrind.sh" "$@" --numstat)
ignoring=$("$fjalar/diff-from-valgrind.sh" "$@" --numstat -w --ignore-blank-lines)
if [ "$plain" = "$ignoring" ]; then
  echo "$0: Fjalar's copies of upstream Valgrind files have upstream's whitespace."
  exit 0
fi
echo "$0: these files differ from upstream Valgrind in whitespace:"
# Each line is a file's numbers, then its numbers when whitespace is ignored
# (0 and 0 if all its changes are whitespace), then its name.
join -t $'\t' -j 3 -a 1 -e 0 -o 1.1,1.2,2.1,2.2,0 \
    <(sort -t $'\t' -k 3 <<< "$plain") <(sort -t $'\t' -k 3 <<< "$ignoring") \
  | awk -F '\t' '$1 != $3 || $2 != $4 { print $5 ": +" $1 " -" $2 ", but +" $3 " -" $4 " ignoring whitespace" }'
# The command is relative to the current directory, as $0 and DIR are.
# --ws-error-highlight=all highlights trailing whitespace in removed lines as
# well as in added lines.
printf 'To see the changes:  %q' "$(dirname -- "$0")/diff-from-valgrind.sh"
printf ' %q' "$@" --ws-error-highlight=all
printf ' -- FILE\n'
exit 1
