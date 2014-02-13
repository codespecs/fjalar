###########################################################################
### Rules
###

### Default tag
help:
	@echo "Targets:"
	@echo " build         -- build all of valgrind and fjalar(includes kvasir)"
	@echo " test          -- build and run valgrind regression tests"
	@echo "               -- see the Daikon tree for fjalar/kvasir regression tests"
	@echo " clean         -- remove basic generated files"
	@echo " very-clean    -- remove (most) all generated files"
	@echo " "

build:
	bash ./auto-everything.sh

test:
	cd valgrind && $(MAKE) regtest

clean:
	cd valgrind && $(MAKE) clean

very-clean:
	cd valgrind/docs && $(MAKE) distclean
	cd valgrind && $(MAKE) uninstall
	cd valgrind && $(MAKE) distclean

