OCB_FLAGS = -use-ocamlfind -use-menhir -I src \
			-pkgs fmt,fmt.tty,alcotest,ocamlgraph,pcre \

OCB = ocamlbuild $(OCB_FLAGS)

GITHASH := $(shell scripts/git-hash)

default: squirrel

all: squirrel test

PROVER_TESTS = $(wildcard tests/ok/*.sp) $(wildcard tests/fail/*.sp)
PROVER_EXAMPLES = $(wildcard examples/*.sp) $(wildcard examples/tutorial/*.sp) $(wildcard examples/stateful/*.sp)

test: squirrel alcotest okfail_test

.PHONY: ok_test ok_test_end alcotest test.byte squirrel squirrel.byte

# Directory for logging test runs
RUNLOGDIR=_build/log
okfail_test:
	rm -rf $(RUNLOGDIR)
	@$(MAKE) -j8 okfail_test_end
	@$(MAKE) -j4 examples_end

okfail_test_end: $(PROVER_TESTS:.sp=.ok)
	@echo
	@if test -f tests/tests.ko ; then \
	  echo Some tests failed: ; \
	  cat tests/tests.ko ; rm -f tests/tests.ko ; exit 1 ; \
	 else echo All tests passed successfully. ; fi

examples_end: $(PROVER_EXAMPLES:.sp=.ok)
	@echo
	@rm -f tests/test_prologue.ok
	@if test -f tests/tests.ko ; then \
	  echo Some tests failed: ; \
	  cat tests/tests.ko ; rm -f tests/tests.ko ; exit 1 ; \
	 else echo All tests passed successfully. ; fi

tests/test_prologue.ok:
	@echo "Running tests/ok/*.sp, tests/fail/*.sp, examples/*.sp, examples/tutorial/*.sp and examples/stateful/*.sp."
%.ok: tests/test_prologue.ok %.sp
	@mkdir -p `dirname $(RUNLOGDIR)/$(@:.ok=.sp)`
	@if ./squirrel $(@:.ok=.sp) \
	  > $(RUNLOGDIR)/$(@:.ok=.sp) \
	  2> $(RUNLOGDIR)/$(@:.ok=.sp.stderr) \
	 ; then echo -n . ; \
	 else echo "[FAIL] $(@:.ok=.sp)" >> tests/tests.ko ; echo -n '!' ; fi

test.byte: version sanity
	$(OCB) test.byte

alcotest: test.byte
	@mkdir -p ./_build/_tests
	@rm -f ./_build/_tests/Squirrel ./_build/_tests/latest
	./test.byte --compact

clean:
	$(OCB) -clean
	@rm -f squirrel
	rm -f *.coverage
	rm -rf _coverage

squirrel.byte: version sanity
	$(OCB) squirrel.byte

debug: version sanity
	$(OCB) -tags debug squirrel.native


squirrel: squirrel.byte
	@ln -s -f squirrel.byte squirrel

makecoverage: version sanity
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

install: version squirrel
	cp squirrel.byte ~/.local/bin/squirrel.byte

doc: squirrel
	$(OCB) -ocamldoc "ocamldoc -stars" squirrel.docdir/index.html

sanity: _build/requirements

version:
	rm -f src/commit.ml
	sed 's/GITHASH/$(GITHASH)/' < src/commit.ml.in > src/commit.ml

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

.PHONY: version clean sanity
