OCB_FLAGS = -use-ocamlfind -use-menhir -I src \
			-pkgs fmt,fmt.tty,alcotest,ocamlgraph

OCB = ocamlbuild $(OCB_FLAGS)

all: byte test

test: byte
	./main.byte

clean:
	$(OCB) -clean
	rm -f sanity

native: sanity
	$(OCB) main.native

byte: sanity
	$(OCB) main.byte

profile: sanity
	$(OCB) -tag profile main.native

debug: sanity
	$(OCB) -tag debug main.byte

# check that menhir is installed
PLEASE="Please install $$pkg, e.g. using \"opam install $$pkg\"." 
sanity: Makefile
	@(echo -n "Checking for menhir... " ; \
	  which menhir ) || ( \
	  pkg=menhir echo $(PLEASE) ; \
	  false )
	@for pkg in ocamlgraph alcotest ; do \
	  (echo -n "Checking for $$pkg... " ; \
	   ocamlfind query $$pkg ) || ( \
	   pkg=$$pkg ; echo $(PLEASE) ; \
	   false ) ; \
	done
	touch sanity

.PHONY: clean byte native profile debug
