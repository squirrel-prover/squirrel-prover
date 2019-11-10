OCB_FLAGS = -use-ocamlfind -use-menhir -I src \
			-pkgs fmt,fmt.tty,alcotest,ocamlgraph

OCB = ocamlbuild $(OCB_FLAGS)

all: metabc test

PROVER_TESTS = examples/lak.mbc \
			   examples/forall.mbc \
			   examples/equality_propagation.mbc \
			   examples/input.mbc \
			   examples/euf_null.mbc \
			   examples/euf_trivial.mbc \
			   examples/euf_basic.mbc \
			   examples/euf_output2.mbc \
			   examples/euf_output3.mbc \
			   examples/axiom.mbc \
			   examples/axiom_collision_resistance.mbc \
#			   examples/euf_output.mbc \
			   examples/macros_input.mbc \
			   examples/macros.mbc \
			   examples/euf.mbc

test: sanity
	$(OCB) test.byte
	./test.byte
	@echo ""
	@tests=0 ; failures=0 ; for f in $(PROVER_TESTS) ; do \
	  echo -n "Running prover on $$f... " ; \
	  tests=$$((tests+1)) ; \
	  if ./metabc $$f > /dev/null 2> /dev/null ; then echo OK ; else \
	  failures=$$((failures+1)) ; echo FAIL ; fi ; \
	done ; \
	echo "Total: $$tests tests, $$failures failures." ; \
	test $$failures -eq 0

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
