###########################################################################
### Rules
###

### Default tag
help:
	@echo "Targets:"
	@echo " build         -- build all of valgrind and fjalar (includes kvasir)"
	@echo " test          -- build and run valgrind regression tests"
	@echo " check-regtest -- run valgrind regression tests; fail on unexpected failures"
	@echo " fjalar-test   -- run the Fjalar regression tests in this repository"
	@echo " daikon-test   -- run Fjalar/Kvasir regression tests from Daikon"
	@echo " check-options -- check that every command-line option is documented"
	@echo " clean         -- remove basic generated files"
	@echo " very-clean    -- remove (most) all generated files"
	@echo " doc           -- build the valgrind-merge documentation"
	@echo " "

build:
	bash ./auto-everything.sh

# Every command-line option must appear in the "--help" usage message.
.PHONY: check-options
check-options:
	./check-options-documented

# Valgrind tests
.PHONY: test
test:
	cd valgrind && $(MAKE) regtest

# Valgrind tests, compared to the expected failures for this OS
.PHONY: check-regtest
check-regtest:
	./check-regtest.sh

# Fjalar tests that do not depend on Daikon: every *-test.sh script.
.PHONY: fjalar-test
fjalar-test:
	for t in valgrind/fjalar/tests/*-test.sh; do echo "Running $$t"; $$t || exit 1; done

# Kvasir tests
.PHONY: daikon-test
daikon-test: ../daikon
	# debugging
	ls -l valgrind/inst/bin/valgrind valgrind/inst/libexec/valgrind/fjalar-amd64-linux
	ls -l ../daikon/fjalar/valgrind/inst/bin/valgrind ../daikon/fjalar/valgrind/inst/libexec/valgrind/fjalar-amd64-linux
	$(MAKE) -C ../daikon compile daikon.jar kvasir
	ls -l valgrind/inst/bin/valgrind valgrind/inst/libexec/valgrind/fjalar-amd64-linux
	ls -l ../daikon/fjalar/valgrind/inst/bin/valgrind ../daikon/fjalar/valgrind/inst/libexec/valgrind/fjalar-amd64-linux
	$(MAKE) -C ../daikon/tests/kvasir-tests clean-all regression-tests

.PHONY: TEMP-daikon-test
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

.PHONY: doc
doc:
	cd doc && $(MAKE) all
