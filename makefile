main : support.cmo syntax.cmo core.cmo lexer.cmo parser.cmo main.cmo
	ocamlc -o main support.cmo syntax.cmo core.cmo lexer.cmo parser.cmo main.cmo

support.cmo :
	ocamlc -c support.mli support.ml
	
syntax.cmo : support.cmo
	ocamlc -c syntax.mli syntax.ml
	
core.cmo : syntax.cmo support.cmo
	ocamlc -c core.mli core.ml

lexer.ml :
	ocamllex lexer.mll

parser.mli parser.ml : parser.ml lexer.ml
	ocamlyacc parser.mly
	
parser.cmi : parser.mli
	ocamlc -c parser.mli
	
lexer.cmo : parser.cmi
	ocamlc -c lexer.ml
	
parser.cmo : parser.cmi lexer.ml
	ocamlc -c parser.ml
	
main.cmo : parser.cmo
	ocamlc -c main.ml

clean :
	rm *.cmo *.cmi main lexer.ml parser.ml parser.mli