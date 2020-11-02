OCB_FLAGS = -use-ocamlfind -use-menhir -I src \
			-pkgs fmt,fmt.tty,alcotest,ocamlgraph,pcre \

OCB = ocamlbuild $(OCB_FLAGS)

default: squirrel

all: squirrel test

PROVER_OK_TESTS = $(wildcard tests/ok/*.sp) $(wildcard examples/*.sp)

test: alcotest ok_test

.PHONY: ok_test ok_test_end alcotest

ok_test:
	@$(MAKE) -j8 ok_test_end
ok_test_end: $(PROVER_OK_TESTS:.sp=.ok)
	@echo
	@rm -f tests/ok/test_prologue.ok
	@if test -f tests/ok/tests.ko ; then \
	  echo Some tests failed: ; \
	  cat tests/ok/tests.ko ; rm -f tests/ok/tests.ko ; exit 1 ; \
	 else echo All tests passed successfully. ; fi
tests/ok/test_prologue.ok:
	@echo "Running tests/ok/*.sp and examples/*.sp."
%.ok: tests/ok/test_prologue.ok %.sp
	@if ./squirrel $(@:.ok=.sp) > /dev/null 2> /dev/null ; then echo -n . ; \
	 else echo "[FAIL] $(@:.ok=.sp)" >> tests/ok/tests.ko ; echo -n '!' ; fi

alcotest: sanity
	$(OCB) test.byte
	@mkdir -p ./_build/_tests
	@rm -f ./_build/_tests/Squirrel ./_build/_tests/latest
	./test.byte --compact

clean:
	$(OCB) -clean
	@rm -f squirrel
	rm -f *.coverage
	rm -rf _coverage

squirrel: sanity
	$(OCB) squirrel.byte
	@ln -s -f squirrel.byte squirrel

makecoverage: sanity
	BISECT_COVERAGE=YES $(OCB) test.byte
	@mkdir -p ./_build/_tests
	@rm -f ./_build/_tests/Squirrel ./_build/_tests/latest
	./test.byte --compact
	BISECT_COVERAGE=YES $(OCB) squirrel.byte
	@ln -s -f squirrel.byte squirrel

coverage: makecoverage ok_test
	@rm -f ./_build/_tests/Squirrel ./_build/_tests/latest
	bisect-ppx-report html --ignore-missing-files
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

install: squirrel
	cp squirrel.byte ~/.local/bin/squirrel.byte

doc: squirrel
	$(OCB) -ocamldoc "ocamldoc -stars" squirrel.docdir/index.html

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
