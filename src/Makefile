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

# use the "-ccopt -static" $(OCAMLC) switch to statically link

# OCAMLC = ocamlcp -p a
#OCAMLC = ocamlopt -p -g
OCAMLC = ocamlopt -ccopt -O2
CMO = cmx
CMA = cmxa
LIBS = str.$(CMA) unix.$(CMA)

all:			L1c L2c L3c L4c L5c
#all:			L1c spill liveness graph L2c L3c L4c L5c

### L5 compiler ###

L5c:	l5_main.$(CMO) l5_parser.$(CMO) l5_lexer.$(CMO) l5_ast.$(CMO) l4_ast.$(CMO) l3_ast.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l5_code.$(CMO) l4_code.$(CMO) l3_code.$(CMO) l2_code.$(CMO) l1_code.$(CMO) utils.$(CMO)
	$(OCAMLC) -o L5c $(LIBS) utils.$(CMO) l1_ast.$(CMO) l2_ast.$(CMO) l3_ast.$(CMO) l4_ast.$(CMO) l5_ast.$(CMO) l1_code.$(CMO) l2_code.$(CMO) l3_code.$(CMO) l4_code.$(CMO) l5_code.$(CMO) l5_parser.$(CMO) l5_lexer.$(CMO) l5_main.$(CMO)

l5_main.$(CMO):	l5_main.ml l5_parser.$(CMO) l5_lexer.$(CMO) l5_ast.$(CMO) l4_ast.$(CMO) l5_code.$(CMO) l4_code.$(CMO) l3_code.$(CMO) l2_code.$(CMO) l1_code.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l5_main.ml

l5_parser.$(CMO):	l5_parser.ml l5_parser.cmi l5_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l5_parser.ml

l5_lexer.$(CMO):	l5_lexer.ml l5_parser.$(CMO) l5_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l5_lexer.ml

l5_code.$(CMO):	l5_code.ml l5_ast.$(CMO) l4_code.$(CMO) l4_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l5_code.ml

l5_parser.cmi:	l5_parser.mli l5_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l5_parser.mli

l5_ast.$(CMO):	l5_ast.ml utils.$(CMO)
		$(OCAMLC) -c l5_ast.ml

l5_parser.ml:	l5_parser.mly
		ocamlyacc l5_parser.mly

l5_parser.mli:	l5_parser.mly
		ocamlyacc l5_parser.mly

l5_lexer.ml:	l5_lexer.mll
		ocamllex l5_lexer.mll

### L4 compiler ###

L4c:	l4_main.$(CMO) l4_parser.$(CMO) l4_lexer.$(CMO) l4_ast.$(CMO) l3_ast.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l4_code.$(CMO) l3_code.$(CMO) l2_code.$(CMO) l1_code.$(CMO) utils.$(CMO)
	$(OCAMLC) -o L4c $(LIBS) utils.$(CMO) l1_ast.$(CMO) l2_ast.$(CMO) l3_ast.$(CMO) l4_ast.$(CMO) l1_code.$(CMO) l2_code.$(CMO) l3_code.$(CMO) l4_code.$(CMO) l4_parser.$(CMO) l4_lexer.$(CMO) l4_main.$(CMO)

l4_main.$(CMO):	l4_main.ml l4_parser.$(CMO) l4_lexer.$(CMO) l4_ast.$(CMO) l3_ast.$(CMO) l4_code.$(CMO) l3_code.$(CMO) l2_code.$(CMO) l1_code.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l4_main.ml

l4_parser.$(CMO):	l4_parser.ml l4_parser.cmi l4_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l4_parser.ml

l4_lexer.$(CMO):	l4_lexer.ml l4_parser.$(CMO) l4_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l4_lexer.ml

l4_code.$(CMO):	l4_code.ml l4_ast.$(CMO) l3_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l4_code.ml

l4_parser.cmi:	l4_parser.mli l4_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l4_parser.mli

l4_ast.$(CMO):	l4_ast.ml utils.$(CMO)
		$(OCAMLC) -c l4_ast.ml

l4_parser.ml:	l4_parser.mly
		ocamlyacc l4_parser.mly

l4_parser.mli:	l4_parser.mly
		ocamlyacc l4_parser.mly

l4_lexer.ml:	l4_lexer.mll
		ocamllex l4_lexer.mll

### L3 compiler ###

L3c:	utils.$(CMO) l3_ast.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l3_code.$(CMO) l2_code.$(CMO) l1_code.$(CMO) l3_parser.$(CMO) l3_lexer.$(CMO) l3_main.$(CMO)
	$(OCAMLC) -o L3c $(LIBS) utils.$(CMO) l3_ast.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l3_code.$(CMO) l2_code.$(CMO) l1_code.$(CMO) l3_parser.$(CMO) l3_lexer.$(CMO) l3_main.$(CMO)

l3_main.$(CMO):	l3_main.ml l3_parser.$(CMO) l3_lexer.$(CMO) l3_ast.$(CMO) l2_ast.$(CMO) l2_code.$(CMO) l1_code.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l3_main.ml

l3_parser.$(CMO):	l3_parser.ml l3_parser.cmi utils.$(CMO)
		$(OCAMLC) -c l3_parser.ml

l3_lexer.$(CMO):	l3_lexer.ml l3_parser.cmi l3_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l3_lexer.ml

l3_code.$(CMO):	l3_code.ml l3_ast.$(CMO) l2_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l3_code.ml

l3_parser.cmi:	l3_parser.mli l3_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l3_parser.mli

l3_ast.$(CMO):	l3_ast.ml utils.$(CMO)
		$(OCAMLC) -c l3_ast.ml

l3_parser.ml:	l3_parser.mly
		ocamlyacc l3_parser.mly

l3_parser.mli:	l3_parser.mly
		ocamlyacc l3_parser.mly

l3_lexer.ml:	l3_lexer.mll
		ocamllex l3_lexer.mll

### graph test ###

graph:			utils.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l2_code.$(CMO) liveness_parser.$(CMO) liveness_lexer.$(CMO) graph_main.$(CMO)
			$(OCAMLC) -o graph $(LIBS) utils.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l2_code.$(CMO) liveness_parser.$(CMO) liveness_lexer.$(CMO) graph_main.$(CMO)

graph_main.$(CMO):		graph_main.ml liveness_parser.$(CMO) liveness_lexer.$(CMO) l2_code.$(CMO) l2_ast.$(CMO) utils.$(CMO)
			$(OCAMLC) -c graph_main.ml

### liveness test ###

liveness:		utils.$(CMO) l2_ast.$(CMO) l1_ast.ml l2_code.$(CMO) liveness_parser.$(CMO) liveness_lexer.$(CMO) liveness_main.$(CMO)
			$(OCAMLC) -o liveness $(LIBS) utils.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l2_code.$(CMO) liveness_parser.$(CMO) liveness_lexer.$(CMO) liveness_main.$(CMO)

liveness_main.$(CMO):	liveness_main.ml liveness_parser.$(CMO) liveness_lexer.$(CMO) l2_code.$(CMO) l2_ast.$(CMO) utils.$(CMO)
			$(OCAMLC) -c liveness_main.ml

liveness_parser.$(CMO):	liveness_parser.ml liveness_parser.cmi utils.$(CMO)
			$(OCAMLC) -c liveness_parser.ml

liveness_lexer.$(CMO):	liveness_lexer.ml liveness_parser.cmi l2_ast.$(CMO) utils.$(CMO)
			$(OCAMLC) -c liveness_lexer.ml

liveness_parser.cmi:	liveness_parser.mli l2_ast.$(CMO) utils.$(CMO)
			$(OCAMLC) -c liveness_parser.mli

liveness_parser.ml:	liveness_parser.mly
			ocamlyacc liveness_parser.mly

liveness_parser.mli:	liveness_parser.mly
			ocamlyacc liveness_parser.mly

liveness_lexer.ml:	liveness_lexer.mll
			ocamllex liveness_lexer.mll

### spill test ###

spill:			utils.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l2_code.$(CMO) spill_parser.$(CMO) spill_lexer.$(CMO) spill_main.$(CMO)
			$(OCAMLC) -o spill $(LIBS) utils.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l2_code.$(CMO) spill_parser.$(CMO) spill_lexer.$(CMO) spill_main.$(CMO)

spill_main.$(CMO):		spill_main.ml spill_parser.$(CMO) spill_lexer.$(CMO) l2_code.$(CMO) l2_ast.$(CMO) utils.$(CMO)
			$(OCAMLC) -c spill_main.ml

spill_parser.$(CMO):	spill_parser.ml spill_parser.cmi utils.$(CMO)
			$(OCAMLC) -c spill_parser.ml

spill_lexer.$(CMO):	spill_lexer.ml spill_parser.cmi l2_ast.$(CMO) utils.$(CMO)
			$(OCAMLC) -c spill_lexer.ml

spill_parser.cmi:	spill_parser.mli l2_ast.$(CMO) utils.$(CMO)
			$(OCAMLC) -c spill_parser.mli

spill_parser.ml:	spill_parser.mly
			ocamlyacc spill_parser.mly

spill_parser.mli:	spill_parser.mly
			ocamlyacc spill_parser.mly

spill_lexer.ml:		spill_lexer.mll
			ocamllex spill_lexer.mll

### L2 compiler ###

L2c:	utils.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l2_code.$(CMO) l1_code.$(CMO) l2_parser.$(CMO) l2_lexer.$(CMO) l2_main.$(CMO)
	$(OCAMLC) -o L2c $(LIBS) utils.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l2_code.$(CMO) l1_code.$(CMO) l2_parser.$(CMO) l2_lexer.$(CMO) l2_main.$(CMO)

l2_main.$(CMO):	l2_main.ml l2_parser.$(CMO) l2_lexer.$(CMO) l2_ast.$(CMO) l1_ast.$(CMO) l1_code.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l2_main.ml

l2_parser.$(CMO):	l2_parser.ml l2_parser.cmi utils.$(CMO)
		$(OCAMLC) -c l2_parser.ml

l2_lexer.$(CMO):	l2_lexer.ml l2_parser.cmi l2_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l2_lexer.ml

l2_code.$(CMO):	l2_code.ml l2_ast.$(CMO) l1_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l2_code.ml

l2_parser.cmi:	l2_parser.mli l2_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l2_parser.mli

l2_ast.$(CMO):	l2_ast.ml utils.$(CMO)
		$(OCAMLC) -c l2_ast.ml

l2_parser.ml:	l2_parser.mly
		ocamlyacc l2_parser.mly

l2_parser.mli:	l2_parser.mly
		ocamlyacc l2_parser.mly

l2_lexer.ml:	l2_lexer.mll
		ocamllex l2_lexer.mll

### L1 compiler ###
L1c:	utils.$(CMO) l1_ast.$(CMO) l1_code.$(CMO) l1_parser.$(CMO) l1_lexer.$(CMO) l1_main.$(CMO)
	$(OCAMLC) -o L1c $(LIBS) utils.$(CMO) l1_ast.$(CMO) l1_code.$(CMO) l1_parser.$(CMO) l1_lexer.$(CMO) l1_main.$(CMO)

l1_main.$(CMO):	l1_main.ml l1_parser.$(CMO) l1_lexer.$(CMO) l1_code.$(CMO) l1_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l1_main.ml

l1_parser.$(CMO):	l1_parser.ml l1_parser.cmi utils.$(CMO)
		$(OCAMLC) -c l1_parser.ml

l1_lexer.$(CMO):	l1_lexer.ml l1_parser.cmi l1_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l1_lexer.ml

l1_code.$(CMO):	l1_code.ml l1_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l1_code.ml

l1_parser.cmi:	l1_parser.mli l1_ast.$(CMO) utils.$(CMO)
		$(OCAMLC) -c l1_parser.mli

l1_ast.$(CMO):	l1_ast.ml utils.$(CMO)
		$(OCAMLC) -c l1_ast.ml

l1_parser.ml:	l1_parser.mly
		ocamlyacc l1_parser.mly

l1_parser.mli:	l1_parser.mly
		ocamlyacc l1_parser.mly

l1_lexer.ml:	l1_lexer.mll
		ocamllex l1_lexer.mll

utils.$(CMO):	utils.ml
		$(OCAMLC) -c utils.ml

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

l2c_tarball:		L2c clean
			tar -cvzf mcclurg.2.tar.gz L2* Makefile l2* l1_code.ml l1_ast.ml utils.ml

l3c_tarball:		L3c clean
			tar -cvzf mcclurg.3.tar.gz L3* Makefile l3* l2_code.ml l1_code.ml l2_ast.ml l1_ast.ml utils.ml

l4c_tarball:		L4c clean
			tar -cvzf mcclurg.4.tar.gz L4* Makefile l4* l3_code.ml l2_code.ml l1_code.ml l3_ast.ml l2_ast.ml l1_ast.ml utils.ml

l5c_tarball:		L5c clean
			tar -cvzf mcclurg.5.tar.gz L5* Makefile l5* l4_code.ml l3_code.ml l2_code.ml l1_code.ml l4_ast.ml l3_ast.ml l2_ast.ml l1_ast.ml utils.ml

wc:		
		make clean
		wc -l *.m* mod_runtime.c
