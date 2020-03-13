OCB_FLAGS = -use-ocamlfind -use-menhir -I src \
			-pkgs fmt,fmt.tty,alcotest,ocamlgraph,pcre \

OCB = ocamlbuild $(OCB_FLAGS)

all: metabc test

PROVER_OK_TESTS = $(wildcard tests/ok/*)

test: alcotest ok_test examples_test

.PHONY: ok_test
ok_test:
	@$(MAKE) -j8 $(PROVER_OK_TESTS:.mbc=.ok)
	@rm -f tests/ok/test_prologue.ok
	@if test -f tests/ok/tests.ko ; then \
	  echo Some tests failed: ; \
	  cat tests/ok/tests.ko ; rm -f tests/ok/tests.ko ; exit 1 ; \
	 else echo All 'tests/ok/*.mbc' passed successfully. ; fi
tests/ok/test_prologue.ok:
	@echo "\n --- Running tests/*/.mbc --- \n"
	@touch $@
%.ok: tests/ok/test_prologue.ok %.mbc
	@if ./metabc $(@:.ok=.mbc) > /dev/null 2> /dev/null ; then echo -n . ; \
	 else echo "[FAIL] $(@:.ok=.mbc)" >> tests/ok/tests.ko ; echo -n '!' ; fi

alcotest: sanity
	$(OCB) test.byte
	./test.byte

examples_test:
	@echo "\n --- Running examples/*.mbc --- \n"
	@tests=0 ; failures=0 ; for f in $(wildcard examples/*.mbc) ; do \
	  echo -n "Running prover on $$f ... " ; \
	  tests=$$((tests+1)) ; \
	  if ./metabc $$f > /dev/null 2> /dev/null ; then echo OK ; else \
	  failures=$$((failures+1)) ; echo FAIL ; fi ; \
	done ; \
	echo "Total: $$tests tests, $$failures failures." ; \
	test $$failures -eq 0

clean:
	$(OCB) -clean
	@rm -f metabc
	rm -f *.coverage
	rm -rf _coverage

metabc: sanity
	$(OCB) metabc.byte
	@ln -s -f metabc.byte metabc

makecoverage: sanity
	BISECT_COVERAGE=YES $(OCB) test.native
	./test.native
	BISECT_COVERAGE=YES $(OCB) metabc.byte
	@ln -s -f metabc.byte metabc

coverage: makecoverage ok_test examples_test
	bisect-ppx-report html -I _build/
	rm -f *.coverage

%.cmo: sanity
	$(OCB) $@

native: sanity
	$(OCB) test.native

byte: sanity
	$(OCB) test.byte

profile: sanity
	$(OCB) -tag profile test.native

debug: sanity
	$(OCB) -tag debug test.byte

install: metabc
	cp metabc.byte ~/.local/bin/metabc.byte

doc: metabc
	$(OCB) -ocamldoc "ocamldoc -stars" metabc.docdir/index.html

sanity: _build/requirements

# check that requirements are installed
PLEASE="Please install $$pkg, e.g. using \"opam install $$pkg\"."
_build/requirements: Makefile
	@(echo -n "Checking for menhir... " ; \
	  which menhir ) || ( \
	  pkg=menhir ; echo $(PLEASE) ; \
	  false )
	@for pkg in fmt ocamlgraph alcotest pcre ; do \
	  (echo -n "Checking for $$pkg... " ; \
	   ocamlfind query $$pkg ) || ( \
	   pkg=$$pkg ; echo $(PLEASE) ; \
	   false ) ; \
	done
	mkdir -p _build
	touch _build/requirements

.PHONY: clean byte native profile debug sanity
