all: main

main: main.byte

test: test.byte

%.byte:
	ocamlbuild -I src -r -use-ocamlfind -pkgs core,llvm -tag thread -use-menhir $@
	mv $@ $*

clean:
	rm -f main test

.PHONY: clean
