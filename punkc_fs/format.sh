mv frontend/parse.fs frontend/parse.fx
mv frontend/parse.fsi frontend/parse.fxi
mv frontend/lex.fs frontend/lex.fx
fantomas . --recurse --preserveEOL
for f in $(find . -name "*.fx"); do mv $f ${f%.*}.fs; done
for f in $(find . -name "*.fxi"); do mv $f ${f%.*}.fsi; done
