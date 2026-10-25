#!/bin/bash

# This script checks that a change leaves Fjalar's output unchanged, including
# the debugging output that Fjalar's copies of Binutils' readelf.c and dwarf.c
# print.  Use it when refactoring those files; see
# plan-reduce-readelf-diffs.md.  The Kvasir tests check only the .decls and
# .dtrace files, not the debugging output.
#
# Usage: ./compare-debug-output.sh [--update] DIR
#
# Build Fjalar ("make build") before running the script.
#
# DIR holds test programs, in DIR/programs/, and Fjalar's output for them.
# If DIR/programs/ does not exist, the script compiles each C and C++ program
# in valgrind/fjalar/tests/ several ways (DWARF 3, 4, and 5; -O0 and -O2; gcc
# and, if it is installed, clang) into it.  Later runs reuse the programs, so
# that a compiler upgrade does not change the output.  To compile them again,
# delete DIR.
#
# For each program, the script runs Fjalar with --no-dyncomp and --decls-only,
# which read the program's debugging information and write the .decls file but
# do not run the program, three times:  with no debugging option, with
# --fjalar-debug-dump, and with --fjalar-debug.  It saves the output of each
# run, which includes the .decls file of the first, with Valgrind's process ID
# replaced by "PID".
#
# If DIR/expected/ does not exist, or with --update, the script saves the
# output there, as the baseline.  Otherwise, it saves the output in
# DIR/actual/, compares it with the baseline, prints the differences, and
# exits with status 1 if there are any.
#
# A typical use:
#   ./compare-debug-output.sh /tmp/$USER/debug-output   # before the change
#   (edit; make build)
#   ./compare-debug-output.sh /tmp/$USER/debug-output   # after the change

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

update=false
if [ "${1-}" = --update ]; then
  update=true
  shift
fi
if [ $# -ne 1 ]; then
  echo "Usage: $0 [--update] DIR" >&2
  exit 2
fi

# The Fjalar tree that contains this script, even if $0 is a symbolic link.
FJALARDIR=$(dirname -- "$(readlink -f -- "$0")")
VALGRIND=$FJALARDIR/valgrind/inst/bin/valgrind
if [ ! -x "$VALGRIND" ]; then
  echo "$0: Fjalar is not built; run \"make build\" in $FJALARDIR." >&2
  exit 2
fi
mkdir -p "$1"
DIR=$(cd "$1" && pwd)
PROGRAMS=$DIR/programs

# Usage: compile_programs
# Compiles the test programs into $PROGRAMS.
compile_programs() {
  local tmp variant name cc cxx compiler flags src base out
  # A temporary directory, renamed at the end, so that an interrupted run
  # leaves no partial set of programs that a later run would reuse.
  tmp=$(mktemp -d "$DIR/programs.XXXXXX")
  # Each variant is a name, a C compiler, a C++ compiler, and flags.
  # Fjalar recognizes a function's entry point only at the address in the
  # debugging information, so the programs must not be position-independent.
  local -a variants=(
    "gcc-dwarf3-O0 gcc g++ -gdwarf-3 -O0"
    "gcc-dwarf4-O0 gcc g++ -gdwarf-4 -O0"
    "gcc-dwarf4-O2 gcc g++ -gdwarf-4 -O2"
    "gcc-dwarf5-O0 gcc g++ -gdwarf-5 -O0"
  )
  if command -v clang > /dev/null && command -v clang++ > /dev/null; then
    variants+=(
      "clang-dwarf4-O0 clang clang++ -gdwarf-4 -O0"
      "clang-dwarf5-O0 clang clang++ -gdwarf-5 -O0"
    )
  fi
  for variant in "${variants[@]}"; do
    read -r name cc cxx flags <<< "$variant"
    for src in "$FJALARDIR"/valgrind/fjalar/tests/*.c "$FJALARDIR"/valgrind/fjalar/tests/*.cc; do
      case $src in
        *.c) compiler=$cc ;;
        *) compiler=$cxx ;;
      esac
      base=$(basename "$src")
      out=$tmp/${base%.*}-${base##*.}-$name
      # Some programs need options or libraries that a variant lacks; the
      # comparison uses whichever programs compiled.
      # shellcheck disable=SC2086 # $flags is a list of options.
      if ! "$compiler" $flags -no-pie -o "$out" "$src" -lm > "$out.log" 2>&1; then
        echo "Skipping $(basename "$out"), which did not compile; see $PROGRAMS/$(basename "$out").log" >&2
        rm -f "$out"
      else
        rm -f "$out.log"
      fi
    done
  done
  mv "$tmp" "$PROGRAMS"
}

# Usage: run_fjalar PROGRAM OUTDIR
# Runs Fjalar on PROGRAM in each configuration, saving the output in OUTDIR.
run_fjalar() {
  local program=$1 outdir=$2 name config status rundir
  local -a options
  name=$(basename "$program")
  # The debugging output contains addresses on Valgrind's stack and heap and
  # on the program's stack.  "setarch -R" disables address space layout
  # randomization, so that they are the same in every run.  They also depend
  # on the arguments and on the environment, including the current
  # directory, which Valgrind copies to the stacks.  So Fjalar runs with the
  # same arguments, an environment that contains only PATH, and a current
  # directory whose name is the same in every run.
  rundir=$DIR/run/$name
  rm -rf "$rundir"
  mkdir -p "$rundir"
  for config in plain dump debug; do
    case $config in
      plain) options=() ;;
      dump) options=(--fjalar-debug-dump) ;;
      debug) options=(--fjalar-debug) ;;
    esac
    status=0
    # With DynComp, which is the default, Fjalar ignores --decls-only.
    (cd "$rundir" \
       && env -i PATH="$PATH" timeout 600 setarch "$(uname -m)" -R \
            "$VALGRIND" --tool=fjalar --no-dyncomp --decls-only --decls-file="$config.decls" \
            "${options[@]}" "$program" > "$config.out" 2>&1) || status=$?
    # The output need not end with a newline.
    if [ -n "$(tail -c 1 "$rundir/$config.out")" ]; then
      echo >> "$rundir/$config.out"
    fi
    echo "Exit status: $status" >> "$rundir/$config.out"
    # Valgrind's messages start with the process ID, as in "==1234==".  A
    # message can start in the middle of a line, after output that did not
    # end with a newline.
    sed -E 's/(==|--)[0-9]+(==|--)/\1PID\2/g' "$rundir/$config.out" \
      > "$outdir/$name.$config.out"
  done
  # The .decls file does not depend on the debugging options.
  if [ -f "$rundir/plain.decls" ]; then
    mv "$rundir/plain.decls" "$outdir/$name.decls"
  fi
  rm -rf "$rundir"
}

if [ ! -d "$PROGRAMS" ]; then
  echo "Compiling the test programs into $PROGRAMS"
  compile_programs
fi

if [ "$update" = true ] || [ ! -d "$DIR/expected" ]; then
  result=expected
else
  result=actual
fi
rm -rf "${DIR:?}/$result.tmp"
mkdir "$DIR/$result.tmp"
echo "Running Fjalar on the programs in $PROGRAMS"
export VALGRIND DIR
export -f run_fjalar
# shellcheck disable=SC2016 # The inner shell expands $1 and $2.
find "$PROGRAMS" -maxdepth 1 -type f -perm -u+x -print0 | sort -z \
  | xargs -0 -P "$(nproc)" -I {} bash -c 'run_fjalar "$1" "$2"' _ {} "$DIR/$result.tmp"
rm -rf "${DIR:?}/run" "${DIR:?}/$result"
mv "$DIR/$result.tmp" "$DIR/$result"

if [ "$result" = expected ]; then
  echo "Saved the baseline in $DIR/expected"
  exit 0
fi
if diff -r -u "$DIR/expected" "$DIR/actual"; then
  echo "The output is the same as the baseline in $DIR/expected"
else
  echo "$0: the output in $DIR/actual differs from the baseline in $DIR/expected" >&2
  exit 1
fi
