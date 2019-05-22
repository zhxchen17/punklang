all: main

main: main.byte

example: example.byte

test: test.byte

%.byte:
	ocamlbuild -I src -r -use-ocamlfind -pkgs llvm,llvm.analysis,oUnit -tags thread -use-menhir $@
	mv $@ $*

parser:
	menhir src/parser.mly

clean:
	rm -rf main test example _build

.PHONY: clean
