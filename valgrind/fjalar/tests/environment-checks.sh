#!/bin/bash

# Functions that a test sources, to handle an environment (a compiler or a
# CPU) that cannot run the test.  The name of this file does not end in
# "-test.sh", so that it is not run as a test itself.

# Fails in continuous integration (GitHub Actions sets CI, and Azure Pipelines
# sets TF_BUILD), and otherwise skips the test, because this environment
# cannot run it.  Failing in continuous integration ensures that a change of
# compilers or machines that makes the test vacuous does not go unnoticed.
# $1 is the name of the test, and $2 is the reason.
unsuitable_environment() {
  if [ -n "${CI:-}" ] || [ -n "${TF_BUILD:-}" ]; then
    echo "$1: FAILED: $2" >&2
    exit 1
  fi
  echo "$1: SKIPPED: $2" >&2
  exit 0
}

# Calls unsuitable_environment unless the CPU has every flag after $1, the
# name of the test.  The flags are as in /proc/cpuinfo.
require_cpu_flags() {
  local name="$1"
  shift
  local flag
  for flag in "$@"; do
    if ! grep -qw "${flag}" /proc/cpuinfo; then
      unsuitable_environment "${name}" "the CPU does not support ${flag}"
    fi
  done
}
