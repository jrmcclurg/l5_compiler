###########################################################
# EECS 322 Compiler Construction
# Northwestern University
# 4/3/2012
#
# L1-to-assembly Compiler
# Spill Test
# Liveness Test
# Graph Test
# L2-to-L1 Compiler
# L3-to-L2 Compiler
# L4-to-L3 Compiler
# L5-to-L4 Compiler
# Jedidiah R. McClurg
# v. 1.0
#
# Makefile
# This builds the project using the OCaml native-code
# compiler.
#
# make         - builds the project (L1c, spill, liveness,
#                                    graph, L2c, L3c, L4c,
#                                    L5c binary)
# make clean   - deletes all intermediate build files
# make wc      - counts the number of lines of code
###########################################################

#all:			L5c
all:			L1c spill liveness graph L2c L3c L4c L5c

### L5 compiler ###

L5c:	l5_main.cmx l5_parser.cmx l5_lexer.cmx l5_ast.cmx l4_ast.cmx l3_ast.cmx l2_ast.cmx l1_ast.cmx l5_code.cmx l4_code.cmx l3_code.cmx l2_code.cmx l1_code.cmx utils.cmx
	ocamlopt -o L5c str.cmxa utils.cmx l1_ast.cmx l2_ast.cmx l3_ast.cmx l4_ast.cmx l5_ast.cmx l1_code.cmx l2_code.cmx l3_code.cmx l4_code.cmx l5_code.cmx l5_parser.cmx l5_lexer.cmx l5_main.cmx

l5_main.cmx:	l5_main.ml l5_parser.cmx l5_lexer.cmx l5_ast.cmx l4_ast.cmx l5_code.cmx l4_code.cmx l3_code.cmx l2_code.cmx l1_code.cmx utils.cmx
		ocamlopt -c l5_main.ml

l5_parser.cmx:	l5_parser.ml l5_parser.cmi l5_ast.cmx utils.cmx
		ocamlopt -c l5_parser.ml

l5_lexer.cmx:	l5_lexer.ml l5_parser.cmx l5_ast.cmx utils.cmx
		ocamlopt -c l5_lexer.ml

l5_code.cmx:	l5_code.ml l5_ast.cmx l4_ast.cmx utils.cmx
		ocamlopt -c l5_code.ml

l5_parser.cmi:	l5_parser.mli l5_ast.cmx utils.cmx
		ocamlopt -c l5_parser.mli

l5_ast.cmx:	l5_ast.ml utils.cmx
		ocamlopt -c l5_ast.ml

l5_parser.ml:	l5_parser.mly
		ocamlyacc l5_parser.mly

l5_parser.mli:	l5_parser.mly
		ocamlyacc l5_parser.mly

l5_lexer.ml:	l5_lexer.mll
		ocamllex l5_lexer.mll

### L4 compiler ###

L4c:	l4_main.cmx l4_parser.cmx l4_lexer.cmx l4_ast.cmx l3_ast.cmx l2_ast.cmx l1_ast.cmx l4_code.cmx l3_code.cmx l2_code.cmx l1_code.cmx utils.cmx
	ocamlopt -o L4c str.cmxa utils.cmx l1_ast.cmx l2_ast.cmx l3_ast.cmx l4_ast.cmx l1_code.cmx l2_code.cmx l3_code.cmx l4_code.cmx l4_parser.cmx l4_lexer.cmx l4_main.cmx

l4_main.cmx:	l4_main.ml l4_parser.cmx l4_lexer.cmx l4_ast.cmx l3_ast.cmx l4_code.cmx l3_code.cmx l2_code.cmx l1_code.cmx utils.cmx
		ocamlopt -c l4_main.ml

l4_parser.cmx:	l4_parser.ml l4_parser.cmi l4_ast.cmx utils.cmx
		ocamlopt -c l4_parser.ml

l4_lexer.cmx:	l4_lexer.ml l4_parser.cmx l4_ast.cmx utils.cmx
		ocamlopt -c l4_lexer.ml

l4_code.cmx:	l4_code.ml l4_ast.cmx l3_ast.cmx utils.cmx
		ocamlopt -c l4_code.ml

l4_parser.cmi:	l4_parser.mli l4_ast.cmx utils.cmx
		ocamlopt -c l4_parser.mli

l4_ast.cmx:	l4_ast.ml utils.cmx
		ocamlopt -c l4_ast.ml

l4_parser.ml:	l4_parser.mly
		ocamlyacc l4_parser.mly

l4_parser.mli:	l4_parser.mly
		ocamlyacc l4_parser.mly

l4_lexer.ml:	l4_lexer.mll
		ocamllex l4_lexer.mll

### L3 compiler ###

L3c:	utils.cmx l3_ast.cmx l2_ast.cmx l1_ast.cmx l3_code.cmx l2_code.cmx l1_code.cmx l3_parser.cmx l3_lexer.cmx l3_main.cmx
	ocamlopt -o L3c str.cmxa utils.cmx l3_ast.cmx l2_ast.cmx l1_ast.cmx l3_code.cmx l2_code.cmx l1_code.cmx l3_parser.cmx l3_lexer.cmx l3_main.cmx

l3_main.cmx:	l3_main.ml l3_parser.cmx l3_lexer.cmx l3_ast.cmx l2_ast.cmx l2_code.cmx l1_code.cmx utils.cmx
		ocamlopt -c l3_main.ml

l3_parser.cmx:	l3_parser.ml l3_parser.cmi utils.cmx
		ocamlopt -c l3_parser.ml

l3_lexer.cmx:	l3_lexer.ml l3_parser.cmi l3_ast.cmx utils.cmx
		ocamlopt -c l3_lexer.ml

l3_code.cmx:	l3_code.ml l3_ast.cmx l2_ast.cmx utils.cmx
		ocamlopt -c l3_code.ml

l3_parser.cmi:	l3_parser.mli l3_ast.cmx utils.cmx
		ocamlopt -c l3_parser.mli

l3_ast.cmx:	l3_ast.ml utils.cmx
		ocamlopt -c l3_ast.ml

l3_parser.ml:	l3_parser.mly
		ocamlyacc l3_parser.mly

l3_parser.mli:	l3_parser.mly
		ocamlyacc l3_parser.mly

l3_lexer.ml:	l3_lexer.mll
		ocamllex l3_lexer.mll

### graph test ###

graph:			utils.cmx l2_ast.cmx l1_ast.cmx l2_code.cmx liveness_parser.cmx liveness_lexer.cmx graph_main.cmx
			ocamlopt -o graph str.cmxa utils.cmx l2_ast.cmx l1_ast.cmx l2_code.cmx liveness_parser.cmx liveness_lexer.cmx graph_main.cmx

graph_main.cmx:		graph_main.ml liveness_parser.cmx liveness_lexer.cmx l2_code.cmx l2_ast.cmx utils.cmx
			ocamlopt -c graph_main.ml

### liveness test ###

liveness:		utils.cmx l2_ast.cmx l1_ast.ml l2_code.cmx liveness_parser.cmx liveness_lexer.cmx liveness_main.cmx
			ocamlopt -o liveness str.cmxa utils.cmx l2_ast.cmx l1_ast.cmx l2_code.cmx liveness_parser.cmx liveness_lexer.cmx liveness_main.cmx

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

spill:			utils.cmx l2_ast.cmx l1_ast.cmx l2_code.cmx spill_parser.cmx spill_lexer.cmx spill_main.cmx
			ocamlopt -o spill str.cmxa utils.cmx l2_ast.cmx l1_ast.cmx l2_code.cmx spill_parser.cmx spill_lexer.cmx spill_main.cmx

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

L2c:	utils.cmx l2_ast.cmx l1_ast.cmx l2_code.cmx l1_code.cmx l2_parser.cmx l2_lexer.cmx l2_main.cmx
	ocamlopt -o L2c str.cmxa utils.cmx l2_ast.cmx l1_ast.cmx l2_code.cmx l1_code.cmx l2_parser.cmx l2_lexer.cmx l2_main.cmx

l2_main.cmx:	l2_main.ml l2_parser.cmx l2_lexer.cmx l2_ast.cmx l1_ast.cmx l1_code.cmx utils.cmx
		ocamlopt -c l2_main.ml

l2_parser.cmx:	l2_parser.ml l2_parser.cmi utils.cmx
		ocamlopt -c l2_parser.ml

l2_lexer.cmx:	l2_lexer.ml l2_parser.cmi l2_ast.cmx utils.cmx
		ocamlopt -c l2_lexer.ml

l2_code.cmx:	l2_code.ml l2_ast.cmx l1_ast.cmx utils.cmx
		ocamlopt -c l2_code.ml

l2_parser.cmi:	l2_parser.mli l2_ast.cmx utils.cmx
		ocamlopt -c l2_parser.mli

l2_ast.cmx:	l2_ast.ml utils.cmx
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

l1_ast.cmx:	l1_ast.ml utils.cmx
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
		rm -rf *.S *.s *.out *.cm* *.o *.mli *_parser.ml *_lexer.ml

binary:		
		as --32 -o prog.o prog.S
		gcc -m32 -c -O2 -o runtime.o runtime.c
		gcc -m32 -o a.out prog.o runtime.o

l1_tarball:		L1c clean
			tar -cvzf mcclurg.1.tar.gz L1* l1* Makefile utils.ml

spill_tarball:		spill clean
			tar -cvzf mcclurg.spill.tar.gz SPILL* spill* Makefile l2_ast.ml l1_ast.ml l2_code.ml utils.ml

liveness_tarball:	liveness clean
			tar -cvzf mcclurg.liveness.tar.gz LIVENESS* liveness* Makefile l2_ast.ml l1_ast.ml l2_code.ml utils.ml

graph_tarball:		graph clean
			tar -cvzf mcclurg.graph.tar.gz GRAPH* graph* liveness_pars* liveness_lex* Makefile l2_ast.ml l1_ast.ml l2_code.ml utils.ml

l2c_tarball:		graph clean
			tar -cvzf mcclurg.2.tar.gz L2* Makefile l2* l1_code.ml l1_ast.ml utils.ml

l3c_tarball:		graph clean
			tar -cvzf mcclurg.3.tar.gz L3* Makefile l3* l2_code.ml l1_code.ml l2_ast.ml l1_ast.ml utils.ml

l4c_tarball:		graph clean
			tar -cvzf mcclurg.4.tar.gz L4* Makefile l4* l3_code.ml l2_code.ml l1_code.ml l3_ast.ml l2_ast.ml l1_ast.ml utils.ml

l5c_tarball:		graph clean
			tar -cvzf mcclurg.5.tar.gz L5* Makefile l5* l4_code.ml l3_code.ml l2_code.ml l1_code.ml l4_ast.ml l3_ast.ml l2_ast.ml l1_ast.ml utils.ml

wc:		
		make clean
		wc -l *.m*

# use the "-ccopt -static" ocamlopt switch to statically link
