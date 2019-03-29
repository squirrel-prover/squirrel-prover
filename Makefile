OCB_FLAGS = -use-ocamlfind -use-menhir -I src \
			-pkgs fmt,fmt.tty,alcotest

OCB = ocamlbuild $(OCB_FLAGS)

all: byte test

test: byte
	./main.byte

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

# check that menhir is installed
sanity:
	@which menhir || ( \
	  echo "Please install menhir, e.g. using \"opam install menhir\"." ; \
	  false )

.PHONY: clean byte native profile debug sanity
