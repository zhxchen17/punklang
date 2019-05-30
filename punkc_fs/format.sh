mv frontend/parse.fs frontend/parse.fx
mv frontend/parse.fsi frontend/parse.fxi
mv frontend/lex.fs frontend/lex.fx
fantomas . --recurse
for f in $(find . -name "*.fx"); mv $f ${f%.*}.fs done
for f in $(find . -name "*.fxi"); mv $f ${f%.*}.fsi done
