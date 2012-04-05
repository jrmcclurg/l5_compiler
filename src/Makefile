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
L1c:	ast.cmx utils.cmx code.cmx l1parser.cmx l1lexer.cmx l1c.cmx
	ocamlopt -o L1c str.cmxa ast.cmx utils.cmx code.cmx l1parser.cmx l1lexer.cmx l1c.cmx

l1c.cmx:	l1c.ml l1parser.cmx l1lexer.cmx code.cmx
		ocamlopt -c l1c.ml

l1parser.cmx:	l1parser.ml l1parser.cmi utils.cmx
		ocamlopt -c l1parser.ml

l1lexer.cmx:	l1lexer.ml l1parser.cmi utils.cmx
		ocamlopt -c l1lexer.ml

code.cmx:	code.ml utils.cmx ast.cmx
		ocamlopt -c code.ml

utils.cmx:	utils.ml ast.cmx
		ocamlopt -c utils.ml

l1parser.cmi:	l1parser.mli ast.cmx
		ocamlopt -c l1parser.mli

ast.cmx:	ast.ml
		ocamlopt -c ast.ml

l1parser.ml:	l1parser.mly
		ocamlyacc l1parser.mly

l1parser.mli:	l1parser.mly
		ocamlyacc l1parser.mly

l1lexer.ml:	l1lexer.mll
		ocamllex l1lexer.mll

clean:		
		rm -rf *.c *.S *.s *.out *.cm* *.o *.mli l1parser.ml l1lexer.ml

tarball:
		tar -cvzf mcclurg.1.tar.gz ast.ml code.ml L1c l1lexer.mll l1c.ml Makefile l1parser.mly README utils.ml

wc:		
		wc -l l1lexer.mll l1parser.mly ast.ml utils.ml l1c.ml code.ml
