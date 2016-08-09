all: html pdf

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
