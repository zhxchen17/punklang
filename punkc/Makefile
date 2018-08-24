all: main

main: main.byte

example: example.byte

test: test.byte

%.byte:
	ocamlbuild -I src -r -use-ocamlfind -pkgs core,llvm,llvm.analysis,oUnit -tags thread -use-menhir $@
	mv $@ $*

clean:
	rm -rf main test example _build

.PHONY: clean
