#!/bin/bash

# This script checks that a change leaves Fjalar's output unchanged, including
# the debugging output that Fjalar's copies of Binutils' readelf.c and dwarf.c
# print.  Use it when refactoring those files.  The Kvasir tests check only the
# .decls and .dtrace files, not the debugging output.
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
# run, with Valgrind's process ID replaced by "PID", and the .decls file of
# each run.  It fails if a run that succeeds writes no .decls file.
#
# If DIR/expected/ does not exist, the script saves the output there, as the
# baseline.  Otherwise, it saves the output in DIR/actual/, compares it with
# the baseline, prints the differences, and exits with status 1 if there are
# any.  The output does not depend on which Fjalar tree runs the script, so
# the baseline can come from one tree (such as the master branch's) and the
# comparison from another.
#
# With --update, the script runs nothing.  It makes the output in
# DIR/actual/, which the last comparison saved, the new baseline.  Use it
# after a comparison whose differences are all intended.
#
# A typical use:
#   ./compare-debug-output.sh /tmp/$USER/debug-output   # before the change
#   (edit; make build)
#   ./compare-debug-output.sh /tmp/$USER/debug-output   # after the change

# Fail the whole script if any command fails, including within a pipeline.
set -e
set -o pipefail

# Make "cd" with a relative directory resolve it against the current
# directory.
unset CDPATH

update=false
if [ "${1-}" = --update ]; then
  update=true
  shift
fi
if [ $# -ne 1 ]; then
  echo "Usage: $0 [--update] DIR" >&2
  exit 2
fi

if [ "$update" = true ]; then
  if [ ! -d "$1/actual" ]; then
    echo "$0: $1/actual does not exist; run $0 $1 first." >&2
    exit 2
  fi
  rm -rf "${1:?}/expected"
  mv "$1/actual" "$1/expected"
  echo "Saved the output of the last comparison as the baseline in $1/expected"
  exit 0
fi

# The Fjalar tree that contains this script, even if $0 is a symbolic link.
FJALARDIR=$(dirname -- "$(readlink -f -- "$0")")
if [ ! -x "$FJALARDIR/valgrind/inst/bin/valgrind" ]; then
  echo "$0: Fjalar is not built; run \"make build\" in $FJALARDIR." >&2
  exit 2
fi
mkdir -p "$1"
DIR=$(cd "$1" && pwd)
PROGRAMS=$DIR/programs

# Valgrind copies the path of its launcher and the path of its lib directory
# into its environment and the program's, so the addresses in the debugging
# output depend on them.  So that the output is the same no matter which
# Fjalar tree runs the script, Fjalar runs from a copy of the launcher in
# DIR, and with VALGRIND_LIB set to a symbolic link in DIR.  A symbolic link
# to the launcher would not do, because the launcher finds its own path from
# /proc/self/exe, which resolves symbolic links.
mkdir -p "$DIR/valgrind"
cp -f "$FJALARDIR/valgrind/inst/bin/valgrind" "$DIR/valgrind/valgrind"
ln -sfn "$FJALARDIR/valgrind/inst/libexec/valgrind" "$DIR/valgrind/lib"
VALGRIND=$DIR/valgrind/valgrind
VALGRIND_LIB=$DIR/valgrind/lib

# Usage: compile_program COMPILER FLAGS SOURCE OUTPUT
# Compiles SOURCE into OUTPUT.  FLAGS is a list of options, separated by
# spaces.
compile_program() {
  local compiler=$1 flags=$2 src=$3 out=$4
  # Some programs need options or libraries that a variant lacks; the
  # comparison uses whichever programs compiled.
  # shellcheck disable=SC2086 # $flags is a list of options.
  if ! "$compiler" $flags -no-pie -o "$out" "$src" -lm > "$out.log" 2>&1; then
    echo "Skipping $(basename "$out"), which did not compile; see $PROGRAMS/$(basename "$out").log" >&2
    rm -f "$out"
  else
    rm -f "$out.log"
  fi
}

# Usage: compile_programs
# Compiles the test programs into $PROGRAMS.
compile_programs() {
  local tmp variant name cc cxx compiler flags src base
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
  export PROGRAMS
  export -f compile_program
  for variant in "${variants[@]}"; do
    read -r name cc cxx flags <<< "$variant"
    for src in "$FJALARDIR"/valgrind/fjalar/tests/*.c "$FJALARDIR"/valgrind/fjalar/tests/*.cc; do
      case $src in
        *.c) compiler=$cc ;;
        *) compiler=$cxx ;;
      esac
      base=$(basename "$src")
      printf '%s\0' "$compiler" "$flags" "$src" "$tmp/${base%.*}-${base##*.}-$name"
    done
  done \
    | xargs -0 -n 4 -P "$(nproc)" bash -e -o pipefail -c 'compile_program "$@"' _
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
  # same arguments, an environment that contains only a fixed PATH and
  # VALGRIND_LIB, and a current directory whose name is the same in every
  # run.
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
       && env -i PATH=/usr/bin:/bin VALGRIND_LIB="$VALGRIND_LIB" \
            timeout 600 setarch "$(uname -m)" -R \
            "$VALGRIND" --tool=fjalar --no-dyncomp --decls-only --decls-file="$config.decls" \
            "${options[@]}" "$program" > "$config.out" 2>&1) || status=$?
    # The output need not end with a newline.
    if [ -n "$(tail -c 1 "$rundir/$config.out")" ]; then
      echo >> "$rundir/$config.out"
    fi
    echo "Exit status: $status" >> "$rundir/$config.out"
    # Valgrind's messages start with the process ID, as in "==1234==".  A
    # message can start in the middle of a line, after output that did not
    # end with a newline.  After an assertion failure, Valgrind also prints
    # the process ID as the thread's "lwpid".
    sed -E -e 's/(==|--)[0-9]+(==|--)/\1PID\2/g' -e 's/\(lwpid [0-9]+\)/(lwpid PID)/g' \
      "$rundir/$config.out" > "$outdir/$name.$config.out"
    if [ -f "$rundir/$config.decls" ]; then
      mv "$rundir/$config.decls" "$outdir/$name.$config.decls"
    elif [ "$status" -eq 0 ]; then
      echo "compare-debug-output.sh: Fjalar succeeded on $name ($config) but wrote no .decls file" >&2
      exit 1
    fi
  done
  rm -rf "$rundir"
}

if [ ! -d "$PROGRAMS" ]; then
  echo "Compiling the test programs into $PROGRAMS"
  compile_programs
fi
if [ -z "$(find "$PROGRAMS" -maxdepth 1 -type f -perm -u+x -print -quit)" ]; then
  echo "$0: no test program compiled; see the .log files in $PROGRAMS," >&2
  echo "then delete $PROGRAMS and re-run this script." >&2
  exit 1
fi

# run_fjalar records each run's exit status rather than stopping, because
# Fjalar fails on some programs.  A failure to start Valgrind or to load
# Fjalar would instead make every run fail the same way, so that the
# comparison would find no differences.
if ! env -i PATH=/usr/bin:/bin VALGRIND_LIB="$VALGRIND_LIB" \
       timeout 600 setarch "$(uname -m)" -R "$VALGRIND" --tool=fjalar --help > /dev/null; then
  echo "$0: cannot run Fjalar ($VALGRIND --tool=fjalar) under timeout and \"setarch -R\"" >&2
  exit 1
fi

if [ ! -d "$DIR/expected" ]; then
  result=expected
else
  result=actual
fi
rm -rf "${DIR:?}/$result.tmp"
mkdir "$DIR/$result.tmp"
echo "Running Fjalar on the programs in $PROGRAMS"
export VALGRIND VALGRIND_LIB DIR
export -f run_fjalar
# The inner shell does not inherit "set -e" and "set -o pipefail".
# shellcheck disable=SC2016 # The inner shell expands $1 and $2.
find "$PROGRAMS" -maxdepth 1 -type f -perm -u+x -print0 | sort -z \
  | xargs -0 -P "$(nproc)" -I {} bash -e -o pipefail -c 'run_fjalar "$1" "$2"' \
      _ {} "$DIR/$result.tmp"
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
