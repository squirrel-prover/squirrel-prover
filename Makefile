OCB_FLAGS   = -use-ocamlfind -use-menhir -I src -pkgs fmt -pkgs fmt.tty

OCB = 		ocamlbuild $(OCB_FLAGS)

all: byte

clean:
	$(OCB) -clean

native: sanity
	$(OCB) main.native

byte: sanity
	$(OCB) main.byte

profile: sanity
	$(OCB) -tag profile main.native

debug: sanity
	$(OCB) -tag debug main.byte

sanity:
	# check that menhir is installed
	@which menhir || ( \
	  echo "Please install menhir, e.g. using \"opam install menhir\"." ; \
	  false )

test: byte
	./scripts/run_tests.sh

.PHONY: clean byte native profile debug sanity
