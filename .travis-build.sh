#!/bin/bash -v

# TODO: The tests ought to work even if $DAIKONDIR is not set.
export DAIKONDIR=`pwd`/../daikon
# On Travis-CI's Ubuntu 12.04 infrastructure, makeinfo does not take the
# --split=chapter command-line argument but texi2html does.
export TEXI2HTML=texi2html

# Temporarily remove "test", until Valgrind changes from upstream are integrated.
# make build test daikon-test
make build daikon-test
