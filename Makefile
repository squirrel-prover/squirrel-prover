OCB_FLAGS = -use-ocamlfind -use-menhir -I src \
			-pkgs fmt,fmt.tty,alcotest,ocamlgraph

OCB = ocamlbuild $(OCB_FLAGS)

all: metabc test

PROVER_OK_TESTS = tests/ok/forall.mbc \
			   tests/ok/equality_propagation.mbc \
			   tests/ok/actions.mbc \
			   tests/ok/input.mbc \
			   tests/ok/euf_null.mbc \
			   tests/ok/euf_trivial.mbc \
			   tests/ok/euf_basic.mbc \
			   tests/ok/euf_output.mbc \
			   tests/ok/euf_output2.mbc \
			   tests/ok/euf_output3.mbc \
			   tests/ok/axiom.mbc \
			   tests/ok/axiom_collision_resistance.mbc \
			   tests/ok/collisions.mbc \
			   tests/ok/macros_input.mbc

PROVER_FAIL_TESTS = tests/fail/existsintro_fail.mbc \
			tests/fail/existsintro_fail2.mbc \
			tests/fail/eufnull.mbc

test: alcotest ok_test fail_test

alcotest: sanity
	$(OCB) test.byte
	./test.byte

ok_test: sanity
	@echo "\n --- Running tests that must succeed --- \n"
	@tests=0 ; failures=0 ; for f in $(PROVER_OK_TESTS) ; do \
	  echo -n "Running prover on $$f... " ; \
	  tests=$$((tests+1)) ; \
	  if ./metabc $$f > /dev/null 2> /dev/null ; then echo OK ; else \
	  failures=$$((failures+1)) ; echo FAIL ; fi ; \
	done ; \
	echo "Total: $$tests tests, $$failures failures." ; \
	test $$failures -eq 0

fail_test: sanity
	@echo "\n --- Running tests that must fail --- \n"
	@tests=0 ; failures=0 ; for f in $(PROVER_FAIL_TESTS) ; do \
	  echo -n "Running prover on $$f... " ; \
	  tests=$$((tests+1)) ; \
	  if ./metabc $$f > /dev/null 2> /dev/null ; then echo OK ; else \
	  failures=$$((failures+1)) ; echo FAIL ; fi ; \
	done ; \
	echo "Total: $$tests tests, $$failures failures." ; echo ; \
	test $$failures -eq $$tests


clean:
	$(OCB) -clean
	@rm -f metabc

metabc: sanity
	$(OCB) metabc.byte
	@ln -s -f metabc.byte metabc

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
	@for pkg in fmt ocamlgraph alcotest ; do \
	  (echo -n "Checking for $$pkg... " ; \
	   ocamlfind query $$pkg ) || ( \
	   pkg=$$pkg ; echo $(PLEASE) ; \
	   false ) ; \
	done
	mkdir -p _build
	touch _build/requirements

.PHONY: clean byte native profile debug sanity
