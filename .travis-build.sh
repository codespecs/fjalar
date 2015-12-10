#!/bin/bash -v

export DAIKONDIR=`pwd`/../daikon

# Temporarily remove "test", until Valgrind changes from upstream are integrated.
# make build test daikon-test
make build daikon-test
