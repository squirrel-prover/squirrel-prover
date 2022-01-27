GITHASH := $(shell scripts/git-hash)

default: squirrel

all: squirrel test

PROVER_TESTS = $(wildcard tests/ok/*.sp) $(wildcard tests/fail/*.sp)
PROVER_EXAMPLES = $(wildcard examples/*.sp) $(wildcard examples/tutorial/*.sp) $(wildcard examples/stateful/*.sp)  $(wildcard examples/postQuantumKE/*.sp)

test: squirrel alcotest okfail_test

.PHONY: ok_test ok_test_end alcotest test.exe squirrel

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
	@echo "Running tests/ok/*.sp, tests/fail/*.sp, examples/*.sp, examples/tutorial/*.sp, examples/stateful/*.sp and examples/postQuantumKE/*.sp."
%.ok: tests/test_prologue.ok %.sp
	@mkdir -p `dirname $(RUNLOGDIR)/$(@:.ok=.sp)`
	@if ./squirrel $(@:.ok=.sp) \
	  > $(RUNLOGDIR)/$(@:.ok=.sp) \
	  2> $(RUNLOGDIR)/$(@:.ok=.sp.stderr) \
	 ; then echo -n . ; \
	 else echo "[FAIL] $(@:.ok=.sp)" >> tests/tests.ko ; echo -n '!' ; fi

test.exe: version sanity
	dune build test.exe
	cp -f _build/default/test.exe test.exe

alcotest: test.exe
	@mkdir -p ./_build/_tests
	@rm -f ./_build/_tests/Squirrel ./_build/_tests/latest
	./test.exe --compact

clean:
	dune clean
	@rm -f squirrel test.exe
	rm -f *.coverage
	rm -rf _coverage

squirrel: version sanity
	dune build squirrel.exe
	cp -f _build/default/squirrel.exe squirrel


# ??? shouldn't it be the other way around?
# since ocamldebug doesn't work with native code
# debug: version sanity
# 	$(OCB) -tags debug squirrel.native
# with Dune: debug flag (-g) enabled by default
debug: version sanity
	dune build squirrel.bc
	cp -f _build/default/squirrel.bc squirrel

# TODO: implement makecoverage / coverage / doc

# makecoverage: version sanity
# 	BISECT_COVERAGE=YES $(OCB) test.exe
# 	@mkdir -p ./_build/_tests
# 	@rm -f ./_build/_tests/Squirrel ./_build/_tests/latest
# 	./test.exe --compact
# 	BISECT_COVERAGE=YES $(OCB) squirrel.byte
# 	@ln -s -f squirrel.byte squirrel

# coverage: makecoverage ok_test
# 	@rm -f ./_build/_tests/Squirrel ./_build/_tests/latest
# 	bisect-ppx-report html --ignore-missing-files
# 	rm -f *.coverage

# %.cmo: sanity
# 	$(OCB) $@

install: version squirrel
	cp squirrel.byte ~/.local/bin/squirrel.byte

# doc: squirrel
# 	$(OCB) -ocamldoc "ocamldoc -stars" squirrel.docdir/index.html

sanity: # _build/requirements

version:
	rm -f src/commit.ml
	sed 's/GITHASH/$(GITHASH)/' < src/commit.ml.in > src/commit.ml

# check that requirements are installed
# NOTE: Dune automatically provides this kind of help, so this looks obsolete
# PLEASE="Please install $$pkg, e.g. using \"opam install $$pkg\"."
# _build/requirements: Makefile
# 	@(echo -n "Checking for menhir... " ; \
# 	  which menhir ) || ( \
# 	  pkg=menhir ; echo $(PLEASE) ; \
# 	  false )
# 	@for pkg in fmt ocamlgraph alcotest pcre ; do \
# 	  (echo -n "Checking for $$pkg... " ; \
# 	   ocamlfind query $$pkg ) || ( \
# 	   pkg=$$pkg ; echo $(PLEASE) ; \
# 	   false ) ; \
# 	done
# 	mkdir -p _build
# 	touch _build/requirements

.PHONY: version clean sanity
