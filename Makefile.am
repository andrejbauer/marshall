ACLOCAL_AMFLAGS = -I build-aux
bin_PROGRAMS = marshall
marshall_SOURCES =
EXTRA_DIST = example.asd src etc COPYRIGHT.txt README.md

# The main program (without the .ml extension)
MARSHALLTARGET=src/marshall

# How to compile
MARSHALLOCAMLBUILD=$(OCAMLBUILD) -use-menhir -lib nums

.PHONY: test test-validate test-clean \
	marshall.byte marshall.native marshall.d.byte marshall.p.native

marshall: marshall.$(BUILDBEST)
	cd $(srcdir) && \
	cp marshall.$(BUILDBEST) marshall

marshall.byte: src/version.ml
	cd $(srcdir) && \
	$(MARSHALLOCAMLBUILD) $(MARSHALLTARGET).byte

marshall.native: src/version.ml
	cd $(srcdir) && \
	$(MARSHALLOCAMLBUILD) $(MARSHALLTARGET).native

marshall.d.byte: src/version.ml
	cd $(srcdir) && $(MARSHALLOCAMLBUILD) $(MARSHALLTARGET).d.byte

marshall.p.native: src/version.ml
	cd $(srcdir) && $(MARSHALLOCAMLBUILD) $(MARSHALLTARGET).p.native

src/version.ml:
	echo "let version=\"$(PACKAGE_VERSION)\";;" > src/version.ml

# Explain parser conflicts in the file parser.conflicts
conflicts:
	cd $(srcdir) ; \
	$(MARSHALLOCAMLBUILD) -yaccflags "--explain" src/parser.mli ; \
	if [ -f $(srcdir)/_build/src/parser.conflicts ]; \
	then \
		mv -f $(srcdir)/_build/src/parser.conflicts .; \
	fi

# "make test" to see if anything broke
test: marshall.$(BUILDBEST)
	cd $(srcdir)/tests && sh ./test.sh

# "make test-validate" to see if anything broke and ask for validation of possibly
# broken things.
test-validate:
	cd $(srcdir)/tests && sh ./test.sh -v

# Clean up tests
test-clean:
	cd $(srcdir) && rm -f tests/*.out tests/*/*.out

clean: test-clean
	cd $(srcdir) && \
	rm -f marshall marshall-$(PACKAGE_VERSION) src/version.ml && \
	ocamlbuild -clean && rm -f parser.conflicts
