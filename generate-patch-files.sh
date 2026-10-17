# This script creates patch files that are used when merging a newer
# version of upstream Valgrind into Fjalar and Kvasir.
# The patch files are produced by "git diff --binary", so that "git apply" can
# add, remove, and change binary, empty, and executable files.  Limiting
# "git diff --no-index" with a pathspec requires Git 2.51 or later.

cd $INV

rm -f coregrind.patch
git diff --no-index --binary --default-prefix valgrind-old valgrind-new ':(exclude,glob)**/.git' > coregrind.patch

rm -f  memcheck.patch
git diff --no-index --binary --default-prefix valgrind-old/memcheck valgrind-new/memcheck ':(exclude,glob)**/.git' ':(exclude,glob)**/docs' ':(exclude,glob)**/tests' > memcheck.patch

rm -f coregrind-Fjalar.diff
diff -ur -xinst -x.git -xfjalar -xMakefile.in -xfjalar/html valgrind-old fjalar/valgrind > coregrind-Fjalar.diff

rm -f memcheck-Fjalar.diff
diff -ur -xinst -x.git -xMakefile.in -xhtml -xdocs -xtests valgrind-old/memcheck fjalar/valgrind/fjalar > memcheck-Fjalar.diff

