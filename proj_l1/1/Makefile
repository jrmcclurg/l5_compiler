l1c:	ast.cmx utils.cmx parser.cmx lexer.cmx main.cmx
	ocamlopt -o L1c str.cmxa ast.cmx utils.cmx parser.cmx lexer.cmx main.cmx

main.cmx:	main.ml parser.cmx lexer.cmx 
		ocamlopt -c main.ml

parser.cmx:	parser.ml parser.cmi utils.cmx
		ocamlopt -c parser.ml

lexer.cmx:	lexer.ml parser.cmi utils.cmx
		ocamlopt -c lexer.ml

utils.cmx:	utils.ml ast.cmx
		ocamlopt -c utils.ml

parser.cmi:	parser.mli ast.cmx
		ocamlopt -c parser.mli

ast.cmx:	ast.ml
		ocamlopt -c ast.ml

parser.ml:	parser.mly
		ocamlyacc parser.mly

parser.mli:	parser.mly
		ocamlyacc parser.mly

lexer.ml:	lexer.mll
		ocamllex lexer.mll

clean:		
		rm -rf *.cm* *.o *.mli parser.ml lexer.ml

wc:		
		wc -l lexer.mll parser.mly ast.ml utils.ml main.ml 
