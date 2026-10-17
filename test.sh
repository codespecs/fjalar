#!/bin/bash

# Fail the whole script if any command fails.
set -e

## Useful for debugging and sometimes for interpreting the script.
# # Output lines of this script as they are read.
# set -o verbose
# # Output expanded lines of this script as they are executed.
# set -o xtrace

# Don't do this: it causes Travis to mysteriously fail.
# export SHELLOPTS

# Get some system info for debugging.
echo "start of system info"
gcc --version
make --version
if command -v lsb_release &> /dev/null ; then
  lsb_release -a
fi
cat /etc/*release
ldd --version
cat /proc/version
find /lib/ | grep -s "libc-" || true
find /lib64/ | grep -s "libc-" || true
echo "end of system info"

if [[ "$OSTYPE" == "darwin"* ]]; then
  JAVA_HOME="${JAVA_HOME:-$(/usr/libexec/java_home)}"
else
  JAVA_HOME="${JAVA_HOME:-$(dirname "$(dirname "$(readlink -f "$(which javac)")")")}"
fi
export JAVA_HOME
echo "JAVA_HOME=$JAVA_HOME"

# TODO: The tests ought to work even if $DAIKONDIR is not set.
export DAIKONDIR="${DAIKONDIR:-$(pwd)/../daikon}"
echo "DAIKONDIR=$DAIKONDIR"


GIT_SCRIPTS="$("$(dirname "$0")"/clone-git-scripts.sh)"
"$GIT_SCRIPTS/git-clone-related" codespecs daikon
ln -s "$(pwd)" "${DAIKONDIR}/fjalar" || true

make check-options

make build

make doc

## Valgrind tests
## Valgrind doesn't pass its own tests ("make test").  ./check-regtest.sh runs
## them and fails only if the set of failing tests differs from the expected
## failures for this operating system.  CI runs it in separate jobs, because it
## takes about 15 minutes.
# ./check-regtest.sh

## Kvasir tests
make MPARG=-j1 daikon-test
