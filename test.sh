#!/bin/bash

# Fail the whole script if any command fails
set -e

## Useful for debugging and sometimes for interpreting the script.
# # Output lines of this script as they are read.
# set -o verbose
# # Output expanded lines of this script as they are executed.
# set -o xtrace

# Doing this causes Travis to mysteriously fail, so don't do this.
# export SHELLOPTS

# Get some system info for debugging.
cat /proc/version
gcc --version
make --version
#find /lib/ | grep -s "libc-"
#find /lib64/ | grep -s "libc-"
echo "end of system info"

# TODO: The tests ought to work even if $DAIKONDIR is not set.
export DAIKONDIR=`pwd`/../daikon

make build

make doc

## Valgrind tests
## Valgrind doesn't pass its own tests ("make test").  So we should have a
## version of the target that determines the current operating system,
## compares the observed failures to the expected failures (those suffered
## by "make test" on a fresh Valgrind installation on that OS), and the
## overall target only fails if the set of failing tests is different.
# make test

## Kvasir tests
## Kvasir does not currently pass all its tests on Ubuntu 14.04 which is
## used by Travis.  We get around this for now by comparing the list of
## failures with an expected list.
## If Travis moves to Ubuntu 16.04, or we can make it work using Docker,
## we should be able to remove this step.
#make MPARG=-j1 daikon-test 2>&1 | tee test.log
#grep FAILED test.log > travis-fail
#diff travis-fail travis-fail.goal
make MPARG=-j1 daikon-test
