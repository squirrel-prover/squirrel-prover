GITHASH := $(shell scripts/git-hash)

default: squirrel

all: squirrel test

PROVER_TESTS = $(wildcard tests/ok/*.sp) $(wildcard tests/fail/*.sp)
PROVER_EXAMPLES = $(wildcard examples/*.sp) $(wildcard examples/tutorial/*.sp) $(wildcard examples/stateful/*.sp)  $(wildcard examples/postQuantumKE/*.sp)

test: squirrel alcotest okfail_test

.PHONY: ok_test ok_test_end alcotest squirrel

# Directory for logging test runs
RUNLOGDIR=_build/squirrel_log
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

alcotest: version
	@mkdir -p ./_build/default/_build/_tests
	@rm -f ./_build/default/_build/_tests/Squirrel ./_build/default/_build/_tests/latest
	dune runtest --force
# TODO: how to pass the --compact flag to the test executable?

clean:
	dune clean
	@rm -f squirrel
	rm -f *.coverage
	rm -rf _coverage

squirrel: version
	dune build squirrel.exe
	cp -f _build/default/squirrel.exe squirrel

# Previously with ocamlbuild:
# squirrel: squirrel.byte
# debug: version
# 	$(OCB) -tags debug squirrel.native
# --> shouldn't it be the other way around??
# since ocamldebug doesn't work with native code
# with Dune: debug flag (-g) enabled by default
debug: version
	dune build squirrel.bc
	cp -f _build/default/squirrel.bc squirrel

makecoverage: version
	@mkdir -p ./_build/default/_build/_tests
	@rm -f ./_build/default/_build/_tests/Squirrel ./_build/default/_build/_tests/latest
	dune runtest --force --instrument-with bisect_ppx
#	BISECT_COVERAGE=YES $(OCB) squirrel.byte
#	@ln -s -f squirrel.byte squirrel

coverage: makecoverage ok_test
	@rm -f ./_build/_tests/Squirrel ./_build/_tests/latest
	bisect-ppx-report html --ignore-missing-files
	rm -f *.coverage

install: version squirrel
	cp squirrel.byte ~/.local/bin/squirrel.byte

doc: # squirrel
	dune build @doc
	@echo "generated documentation in _build/default/_doc/_html/squirrel/index.html"

version:
	rm -f src/commit.ml
	sed 's/GITHASH/$(GITHASH)/' < src/commit.ml.in > src/commit.ml

.PHONY: version clean
