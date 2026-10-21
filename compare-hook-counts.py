#! /usr/bin/env python3
r"""Compare how often each hook name occurs in two versions of a C file.

Usage: compare-hook-counts.py HOOKS OLD NEW NAME
  HOOKS is a file with one hook name per line.
  OLD and NEW are the two versions of the C file.
  NAME is the name of the C file, which is printed in the output.

For each hook whose count differs between OLD and NEW, in sorted order, prints
  NAME HOOK OLDCOUNT NEWCOUNT
An occurrence is a whole word, so "foo" does not occur in "foo_bar".
This script is called by check-hook-counts.sh.
"""

import collections
import re
import sys


def hook_counts(path, hooks):
    """Return a Counter of the occurrences of each element of hooks in the file."""
    with open(path) as f:
        words = re.findall(r"[A-Za-z0-9_]+", f.read())
    return collections.Counter(w for w in words if w in hooks)


def main():
    if len(sys.argv) != 5:
        sys.exit("Usage: compare-hook-counts.py HOOKS OLD NEW NAME")
    hooks_file, old_file, new_file, name = sys.argv[1:]
    with open(hooks_file) as f:
        hooks = set(f.read().split())
    old = hook_counts(old_file, hooks)
    new = hook_counts(new_file, hooks)
    for hook in sorted(hooks):
        if old[hook] != new[hook]:
            print(name, hook, old[hook], new[hook])


if __name__ == "__main__":
    main()
