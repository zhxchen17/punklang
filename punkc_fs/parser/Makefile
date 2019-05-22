all: parse.fsy lex.fsl

parse.mly: parser.mly
	menhir --only-preprocess-for-ocamlyacc $< > $@

parse.fsy: parse.mly
	echo "%{" > $@
	echo "#light \"off\"" >> $@
	echo "open Tir" >> $@
	cat $< | sed -e '/%{/d' \
	             -e '/^open /d' \
	             -e '/%token/s/[a-zA-Z0-9_]*\.//g' \
	             -e '/%type/s/[a-zA-Z0-9_]*\.//g' \
	             -e '/%token.*->.*/d' \
	             -e '/%type.*->.*/d' \
	             -e 's/Option\.is_some/Option\.isSome/g' \
	       | cat -s >> $@

lex.fsl: lexer.mll
	echo "{" > $@
	echo "module Lexer" >> $@
	echo "#light \"off\"" >> $@
	echo "open Parser" >> $@
	echo "#nowarn \"62\"" >> $@
	echo "open FSharp.Compatibility.OCaml" >> $@
	echo "open FSharp.Text.Lexing" >> $@
	echo "open Config" >> $@
	echo "open Errors" >> $@
	cat $< | sed -e '/^{/d' \
	             -e 's/Lexing\.lexeme/LexBuffer<char>\.LexemeString/g' \
	             -e '/^open /d' \
	       | cat -s >> $@

clean:
	rm lex.fsl parse.fsy

.PHONY: clean
