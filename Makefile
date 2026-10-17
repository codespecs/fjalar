###########################################################################
### Rules
###

### Default tag
help:
	@echo "Targets:"
	@echo " build         -- build all of valgrind and fjalar (includes kvasir)"
	@echo " test          -- build and run valgrind regression tests"
	@echo " fjalar-test   -- run the Fjalar regression tests in this repository"
	@echo " daikon-test   -- run Fjalar/Kvasir regression tests from Daikon"
	@echo " check-options -- check that every command-line option is documented"
	@echo " clean         -- remove basic generated files"
	@echo " very-clean    -- remove (most) all generated files"
	@echo " git-update    -- add/remove files as result of Valgrind merge"
	@echo " doc           -- build the valgrind-merge documentation"
	@echo " "

build:
	bash ./auto-everything.sh

# Every command-line option must appear in the "--help" usage message.
.PHONY: check-options
check-options:
	./check-options-documented

# Valgrind tests
test:
	cd valgrind && $(MAKE) regtest

# Fjalar tests that do not depend on Daikon
fjalar-test:
	valgrind/fjalar/tests/library-compilation-unit-test.sh

# Kvasir tests
daikon-test: ../daikon
	# debugging
	ls -l valgrind/inst/bin/valgrind valgrind/inst/libexec/valgrind/fjalar-amd64-linux
	ls -l ../daikon/fjalar/valgrind/inst/bin/valgrind ../daikon/fjalar/valgrind/inst/libexec/valgrind/fjalar-amd64-linux
	$(MAKE) -C ../daikon compile daikon.jar kvasir
	ls -l valgrind/inst/bin/valgrind valgrind/inst/libexec/valgrind/fjalar-amd64-linux
	ls -l ../daikon/fjalar/valgrind/inst/bin/valgrind ../daikon/fjalar/valgrind/inst/libexec/valgrind/fjalar-amd64-linux
	$(MAKE) -C ../daikon/tests/kvasir-tests clean-all regression-tests

TEMP-daikon-test: ../daikon
	$(MAKE) -C ../daikon compile daikon.jar kvasir
	$(MAKE) -C ../daikon/tests/kvasir-tests clean-all TEMP-regression-tests

../daikon:
	cd .. && git clone https://github.com/codespecs/daikon.git

clean:
	cd valgrind && $(MAKE) clean

very-clean:
	cd valgrind && $(MAKE) uninstall
	cd valgrind && $(MAKE) distclean
	rm -rf valgrind/config.h.in
	rm -rf valgrind/aclocal.m4
	rm -rf valgrind/configure
	rm -rf valgrind/autom4te.cache
	rm -rf valgrind/Makefile.in
	rm -rf valgrind/Makefile.vex.in

# Print the git commands that add and remove files as a result of a Valgrind
# merge.  Review the output, then run it.  Uses ../coregrind.patch and
# ../memcheck.patch, made by generate-patch-files.sh.
#  * Those patches are made with "diff --unidirectional-new-file", which shows
#    a file that is new upstream as a diff against an empty file dated at the
#    epoch (1969-12-31 or 1970-01-01, depending on the time zone).
#  * A file or directory that upstream removed shows up as "Only in
#    valgrind-old...: NAME".
#  * Fjalar's copy of memcheck is valgrind/fjalar/, not valgrind/memcheck/.
EPOCH_RE = [[:space:]](1969-12-31|1970-01-01) 
.PHONY: git-update
git-update:
	@echo "# Files added upstream"
	@grep -E '^--- .*$(EPOCH_RE)' ../coregrind.patch | cut -f1 | cut -d' ' -f2 \
	  | sed -e 's|^valgrind-old/|valgrind/|' -e 's/^/git add /'
	@echo "# Files and directories removed upstream"
	@grep '^Only in valgrind-old' ../coregrind.patch | sed -E 's|^Only in (.*): (.*)$$|\1/\2|' \
	  | sed -e 's|^valgrind-old/|valgrind/|' -e 's/^/git rm -r /'
	@echo "# Memcheck files added upstream; Fjalar may not need all of them"
	@grep -E '^--- valgrind-old/memcheck/.*$(EPOCH_RE)' ../memcheck.patch | cut -f1 | cut -d' ' -f2 \
	  | sed -e 's|^valgrind-old/memcheck/|valgrind/fjalar/|' -e 's/^/git add /'
	@echo "# Memcheck files and directories removed upstream; check for Fjalar changes"
	@grep '^Only in valgrind-old/memcheck' ../memcheck.patch | sed -E 's|^Only in (.*): (.*)$$|\1/\2|' \
	  | sed -e 's|^valgrind-old/memcheck/|valgrind/fjalar/|' -e 's/^/git rm -r /'

.PHONY: doc
doc:
	cd doc && $(MAKE) all
