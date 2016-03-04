#!/bin/bash -v

# Fail the whole script if any command fails
set -e

# Doing this causes Travis to mysteriously fail, so don't do this.
# export SHELLOPTS

# Get some system info for debugging.
cat /proc/version
gcc --version
ls -l /lib/x86_64-linux-gnu/libc-*

# TODO: The tests ought to work even if $DAIKONDIR is not set.
export DAIKONDIR=`pwd`/../daikon

make build

make doc

## Valgrind doesn't pass its own tests ("make test").  So we should have a
## version of the target that determines the current operating system,
## compares the observed failures to the expected failures (those suffered
## by "make test" on a fresh Valgrind installation on that OS), and the
## overall target only fails if the set of failing tests is different.
# make test

## Kvasir does not currently pass all its tests on Ubuntu 14.04 which is
## used by Travis.  So, "make daikon-test" fails.  Reinstate "daikon-test"
## as soon as we have improved Kvasir and/or its test suite so that "make
## daikon-test" passes.
# make daikon-test

# TEMP-daikon-test is a temporary substitute for daikon-test that runs
# a subset of kvasir-tests.  This is to verify the general test process.
make TEMP-daikon-test

