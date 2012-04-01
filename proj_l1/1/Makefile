###########################################################
# EECS 322 Compiler Construction
# Northwestern University
# 4/3/2012
#
# L1-to-assembly Compiler
# Jedidiah R. McClurg
# v. 1.0
#
# Makefile
# This builds the project using the OCaml native-code
# compiler.
#
# make         - builds the project (L1c binary)
# make clean   - deletes all intermediate build files
# make wc      - counts the number of lines of code
###########################################################

# use the "-ccopt -static" ocamlopt switch to statically link
L1c:	ast.cmx utils.cmx code.cmx parser.cmx lexer.cmx main.cmx
	ocamlopt -o L1c str.cmxa ast.cmx utils.cmx code.cmx parser.cmx lexer.cmx main.cmx

main.cmx:	main.ml parser.cmx lexer.cmx code.cmx
		ocamlopt -c main.ml

parser.cmx:	parser.ml parser.cmi utils.cmx
		ocamlopt -c parser.ml

lexer.cmx:	lexer.ml parser.cmi utils.cmx
		ocamlopt -c lexer.ml

code.cmx:	code.ml utils.cmx ast.cmx
		ocamlopt -c code.ml

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
		rm -rf *.c *.S *.out *.cm* *.o *.mli parser.ml lexer.ml

wc:		
		wc -l lexer.mll parser.mly ast.ml utils.ml main.ml code.ml
