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
L1c:	utils.cmx l1_ast.cmx l1_code.cmx l1_parser.cmx l1_lexer.cmx l1_main.cmx
	ocamlopt -o L1c str.cmxa utils.cmx l1_ast.cmx l1_code.cmx l1_parser.cmx l1_lexer.cmx l1_main.cmx

l1_main.cmx:	l1_main.ml l1_parser.cmx l1_lexer.cmx l1_code.cmx l1_ast.cmx utils.cmx
		ocamlopt -c l1_main.ml

l1_parser.cmx:	l1_parser.ml l1_parser.cmi utils.cmx
		ocamlopt -c l1_parser.ml

l1_lexer.cmx:	l1_lexer.ml l1_parser.cmi l1_ast.cmx utils.cmx
		ocamlopt -c l1_lexer.ml

l1_code.cmx:	l1_code.ml l1_ast.cmx utils.cmx
		ocamlopt -c l1_code.ml

l1_parser.cmi:	l1_parser.mli l1_ast.cmx utils.cmx
		ocamlopt -c l1_parser.mli

l1_ast.cmx:	l1_ast.ml utils.ml
		ocamlopt -c l1_ast.ml

utils.cmx:	utils.ml
		ocamlopt -c utils.ml

l1_parser.ml:	l1_parser.mly
		ocamlyacc l1_parser.mly

l1_parser.mli:	l1_parser.mly
		ocamlyacc l1_parser.mly

l1_lexer.ml:	l1_lexer.mll
		ocamllex l1_lexer.mll

clean:		
		rm -rf *.c *.S *.s *.out *.cm* *.o *.mli l1_parser.ml l1_lexer.ml

tarball:
		tar -cvzf mcclurg.1.tar.gz ast.ml code.ml L1c l1_lexer.mll l1_main.ml Makefile l1_parser.mly README utils.ml

wc:		
		wc -l l1_lexer.mll l1_parser.mly ast.ml utils.ml l1_main.ml code.ml
