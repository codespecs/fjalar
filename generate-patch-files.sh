# This script creates patch files that are used when merging a newer
# version of upstream Valgrind into Fjalar and Kvasir.

cd $INV

rm -f coregrind.patch
diff -ur --unidirectional-new-file -x.svn valgrind-old valgrind-new > coregrind.patch

rm -f  memcheck.patch
diff -ur --unidirectional-new-file -x.svn -xdocs -xtests valgrind-old/memcheck valgrind-new/memcheck > memcheck.patch

rm -f coregrind-Fjalar.diff
diff -ur -xinst -x.svn -xfjalar -xMakefile.in -xfjalar/html valgrind-old fjalar/valgrind > coregrind-Fjalar.diff

rm -f memcheck-Fjalar.diff
diff -ur -xinst -x.svn -xMakefile.in -xhtml -xdocs -xtests valgrind-old/memcheck fjalar/valgrind/fjalar > memcheck-Fjalar.diff

