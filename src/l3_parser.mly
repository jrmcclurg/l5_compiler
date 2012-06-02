/*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/7/2012
 *
 * L3-to-L2 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l3_parser.mly
 * This is the specification for the L3 parser, to be
 * used with ocamlyacc.
 */
%{
   open L3_ast;;
   open Utils;;
%}
%token <int32> INT
%token <int> LABEL
%token <int> IDENT 
%token CLOSUREPROC CLOSUREVARS MAKECLOSURE NEWARRAY NEWTUPLE PRINT
%token ASET AREF ALEN NUMBERQ ARRAYQ
%token LET IF
%token LPAREN RPAREN LBRACK RBRACK
%token PLUS MINUS TIMES
%token LEQ LT EQ
%token EOF
/* last tokens have highest precedence */
%start main /* the entry point */
%type <L3_ast.program> main
%%
main:
   LPAREN exp func_list RPAREN { Program(get_current_pos (), $2, $3) }
   /* TODO XXX - add EOF here at some point */ 
;

func:
   | LPAREN LABEL LPAREN var_list RPAREN exp RPAREN {
      Function(get_current_pos (), $2, $4, $6)
   }
;

func_list:
                   { [] }
  | func func_list { $1::$2 }
;

exp:
   | LPAREN LET LPAREN LBRACK var dexp RBRACK RPAREN exp RPAREN { LetExp(get_current_pos (), $5, $6, $9) }
   | LPAREN LET LPAREN LPAREN var dexp RPAREN RPAREN exp RPAREN { LetExp(get_current_pos (), $5, $6, $9) }
   | LPAREN IF sval exp exp RPAREN                              { IfExp(get_current_pos (), $3, $4, $5) }
   | dexp                                                       { DExpExp(get_current_pos (), $1) }
;

dexp:
   | LPAREN PLUS sval sval RPAREN          { PlusDExp(get_current_pos (), $3, $4) }
   | LPAREN MINUS sval sval RPAREN         { MinusDExp(get_current_pos (), $3, $4) }
   | LPAREN TIMES sval sval RPAREN         { TimesDExp(get_current_pos (), $3, $4) }
   | LPAREN LT sval sval RPAREN            { LtDExp(get_current_pos (), $3, $4) }
   | LPAREN LEQ sval sval RPAREN           { LeqDExp(get_current_pos (), $3, $4) }
   | LPAREN EQ sval sval RPAREN            { EqDExp(get_current_pos (), $3, $4) }
   | LPAREN NUMBERQ sval RPAREN            { NumberPredDExp(get_current_pos (), $3) }
   | LPAREN ARRAYQ sval RPAREN             { ArrayPredDExp(get_current_pos (), $3) }
   | LPAREN sval sval_list RPAREN          { AppDExp(get_current_pos (), $2, $3) (* TODO - can the parens be empty? *) }
   | LPAREN NEWARRAY sval sval RPAREN      { NewArrayDExp(get_current_pos (), $3, $4) }
   | LPAREN NEWTUPLE dexp_list RPAREN      { NewTupleDExp(get_current_pos (), $3) }
   | LPAREN AREF sval sval RPAREN          { ArefDExp(get_current_pos (), $3, $4) }
   | LPAREN ASET sval sval sval RPAREN     { AsetDExp(get_current_pos (), $3, $4, $5, true) }
   | LPAREN ALEN sval RPAREN               { AlenDExp(get_current_pos (), $3) }
   | LPAREN PRINT sval RPAREN              { PrintDExp(get_current_pos (), $3) }
   | LPAREN MAKECLOSURE LABEL sval RPAREN  { MakeClosureDExp(get_current_pos (), $3, $4) }
   | LPAREN CLOSUREPROC sval RPAREN        { ClosureProcDExp(get_current_pos (), $3) }
   | LPAREN CLOSUREVARS sval RPAREN        { ClosureVarsDExp(get_current_pos (), $3) }
   | sval                                  { SValDExp(get_current_pos (), $1) }
;

dexp_list:
                    { [] }
   | dexp dexp_list { $1::$2 }
;

var:
   | IDENT { Var(get_current_pos (), $1) }
;

var_list:
                     { [] }
   | var var_list { $1::$2 }
;

sval:
   | var   { VarSVal(get_current_pos(), $1) }
   | INT   { IntSVal(get_current_pos(), $1) }
   | LABEL { LabelSVal(get_current_pos(), $1) }
;

sval_list:
   |                { [] }
   | sval sval_list { $1::$2 }
;
