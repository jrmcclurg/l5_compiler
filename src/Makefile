###########################################################
# EECS 322 Compiler Construction
# Northwestern University
# 4/3/2012
#
# L1-to-assembly Compiler
# Spill Test
# Liveness Test
# Jedidiah R. McClurg
# v. 1.0
#
# Makefile
# This builds the project using the OCaml native-code
# compiler.
#
# make         - builds the project (L1c, spill, liveness binary)
# make clean   - deletes all intermediate build files
# make wc      - counts the number of lines of code
###########################################################

all:			L1c spill liveness L2c

### liveness test ###

liveness:		utils.cmx l2_ast.cmx l2_code.cmx liveness_parser.cmx liveness_lexer.cmx liveness_main.cmx
			ocamlopt -o liveness str.cmxa utils.cmx l2_ast.cmx l2_code.cmx liveness_parser.cmx liveness_lexer.cmx liveness_main.cmx

liveness_main.cmx:	liveness_main.ml liveness_parser.cmx liveness_lexer.cmx l2_code.cmx l2_ast.cmx utils.cmx
			ocamlopt -c liveness_main.ml

liveness_parser.cmx:	liveness_parser.ml liveness_parser.cmi utils.cmx
			ocamlopt -c liveness_parser.ml

liveness_lexer.cmx:	liveness_lexer.ml liveness_parser.cmi l2_ast.cmx utils.cmx
			ocamlopt -c liveness_lexer.ml

liveness_parser.cmi:	liveness_parser.mli l2_ast.cmx utils.cmx
			ocamlopt -c liveness_parser.mli

liveness_parser.ml:	liveness_parser.mly
			ocamlyacc liveness_parser.mly

liveness_parser.mli:	liveness_parser.mly
			ocamlyacc liveness_parser.mly

liveness_lexer.ml:	liveness_lexer.mll
			ocamllex liveness_lexer.mll

### spill test ###

spill:			utils.cmx l2_ast.cmx l2_code.cmx spill_parser.cmx spill_lexer.cmx spill_main.cmx
			ocamlopt -o spill str.cmxa utils.cmx l2_ast.cmx l2_code.cmx spill_parser.cmx spill_lexer.cmx spill_main.cmx

spill_main.cmx:		spill_main.ml spill_parser.cmx spill_lexer.cmx l2_code.cmx l2_ast.cmx utils.cmx
			ocamlopt -c spill_main.ml

spill_parser.cmx:	spill_parser.ml spill_parser.cmi utils.cmx
			ocamlopt -c spill_parser.ml

spill_lexer.cmx:	spill_lexer.ml spill_parser.cmi l2_ast.cmx utils.cmx
			ocamlopt -c spill_lexer.ml

spill_parser.cmi:	spill_parser.mli l2_ast.cmx utils.cmx
			ocamlopt -c spill_parser.mli

spill_parser.ml:	spill_parser.mly
			ocamlyacc spill_parser.mly

spill_parser.mli:	spill_parser.mly
			ocamlyacc spill_parser.mly

spill_lexer.ml:		spill_lexer.mll
			ocamllex spill_lexer.mll

### L2 compiler ###

L2c:	utils.cmx l2_ast.cmx l2_parser.cmx l2_lexer.cmx l2_main.cmx
	ocamlopt -o L2c str.cmxa utils.cmx l2_ast.cmx l2_parser.cmx l2_lexer.cmx l2_main.cmx

l2_main.cmx:	l2_main.ml l2_parser.cmx l2_lexer.cmx l2_ast.cmx utils.cmx
		ocamlopt -c l2_main.ml

l2_parser.cmx:	l2_parser.ml l2_parser.cmi utils.cmx
		ocamlopt -c l2_parser.ml

l2_lexer.cmx:	l2_lexer.ml l2_parser.cmi l2_ast.cmx utils.cmx
		ocamlopt -c l2_lexer.ml

l2_code.cmx:	l2_code.ml l2_ast.cmx utils.cmx
		ocamlopt -c l2_code.ml

l2_parser.cmi:	l2_parser.mli l2_ast.cmx utils.cmx
		ocamlopt -c l2_parser.mli

l2_ast.cmx:	l2_ast.ml utils.ml
		ocamlopt -c l2_ast.ml

l2_parser.ml:	l2_parser.mly
		ocamlyacc l2_parser.mly

l2_parser.mli:	l2_parser.mly
		ocamlyacc l2_parser.mly

l2_lexer.ml:	l2_lexer.mll
		ocamllex l2_lexer.mll

### L1 compiler ###
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

l1_parser.ml:	l1_parser.mly
		ocamlyacc l1_parser.mly

l1_parser.mli:	l1_parser.mly
		ocamlyacc l1_parser.mly

l1_lexer.ml:	l1_lexer.mll
		ocamllex l1_lexer.mll

utils.cmx:	utils.ml
		ocamlopt -c utils.ml

clean:		
		rm -rf *.c *.S *.s *.out *.cm* *.o *.mli *_parser.ml *_lexer.ml

binary:		
		as --32 -o prog.o prog.S
		gcc -m32 -c -O2 -o runtime.o runtime.c
		gcc -m32 -o a.out prog.o runtime.o

l1_tarball:	L1c clean
		tar -cvzf mcclurg.1.tar.gz L1* l1* Makefile utils.ml

spill_tarball:	spill clean
		tar -cvzf mcclurg.spill.tar.gz SPILL* spill* Makefile l2_ast.ml l2_code.ml utils.ml

wc:		
		wc -l *.m*

# use the "-ccopt -static" ocamlopt switch to statically link
