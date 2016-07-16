###########################################################################
### Rules
###

### Default tag
help:
	@echo "Targets:"
	@echo " build         -- build all of valgrind and fjalar (includes kvasir)"
	@echo " test          -- build and run valgrind regression tests"
	@echo " daikon-test   -- run Fjalar/Kvasir regression tests from Daikon"
	@echo " clean         -- remove basic generated files"
	@echo " very-clean    -- remove (most) all generated files"
	@echo " git-update    -- add/remove files as result of Valgrind merge"
	@echo " doc           -- build the valgrind-merge documentation"
	@echo " "

build:
	bash ./auto-everything.sh

# Valgrind tests
test:
	cd valgrind && $(MAKE) regtest

# Kvasir tests
daikon-test: ../daikon
	$(MAKE) -C ../daikon compile daikon.jar kvasir
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

git-update:
	@grep -q '^\-\-\-.*1969\-12\-31' ../coregrind.patch; \
	if [ $$? -eq 0 ]; then \
	  echo git add `grep '^\-\-\-.*1969\-12\-31' ../coregrind.patch | cut --fields=1 | cut -d ' ' --fields=2 | perl -p -e 's/^valgrind-old/valgrind/g'`; \
	fi

	@grep -q '^Only in valgrind-old' ../coregrind.patch; \
	if [ $$? -eq 0 ]; then \
	  echo git rm `grep '^Only in valgrind-old' ../coregrind.patch | perl -p -e 's/: /\//g' | cut -d ' ' --fields=3 | perl -p -e 's/^valgrind-old/valgrind/g'`; \
	fi

	@grep -q '^\-\-\-.*1969\-12\-31' ../memcheck.patch; \
	if [ $$? -eq 0 ]; then \
	  echo add `grep '^\-\-\-.*1969\-12\-31' ../memcheck.patch| cut --fields=1 | cut -d ' ' --fields=2 | perl -p -e 's/^valgrind-old/valgrind/g'`; \
	fi

	@grep -q '^\+\+\+.*1969\-12\-31' ../memcheck.patch; \
	if [ $$? -eq 0 ]; then \
	  echo remove `grep '^\+\+\+.*1969\-12\-31' ../memcheck.patch| cut --fields=1 | cut -d ' ' --fields=2 | perl -p -e 's/^valgrind-new/valgrind/g'`; \
	fi

doc: html pdf

html: valgrind-merge.html

valgrind-merge.html: valgrind-merge.texinfo
	makeinfo --html --no-split $<
# Fixup 'bad' href inserted by makeinfo.
	perl -pi -e 's|dir.html#Top|index.html|;' $@

pdf: valgrind-merge.pdf

valgrind-merge.pdf: valgrind-merge.texinfo
	makeinfo --pdf $<

# -u switch to hunspell is undocumented and subject to change,
# but gives a line number whereas -l does not.
spell-check:
	perl $(DAIKONDIR)/doc/prepare-texinfo-for-spellcheck.pl < valgrind-merge.texinfo | hunspell -u -p $(DAIKONDIR)/doc/daikon.dict
