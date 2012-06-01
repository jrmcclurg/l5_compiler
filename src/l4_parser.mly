/*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/14/2012
 *
 * L4-to-L3 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l4_parser.mly
 * This is the specification for the L4 parser, to be
 * used with ocamlyacc.
 */
%{
   open L4_ast;;
   open Utils;;
%}
%token <int32> INT
%token <int> LABEL
%token <int> IDENT 
%token CLOSUREPROC CLOSUREVARS MAKECLOSURE NEWARRAY NEWTUPLE PRINT
%token ASET AREF ALEN NUMBERQ ARRAYQ BEGIN
%token LET IF
%token LPAREN RPAREN LBRACK RBRACK
%token PLUS MINUS TIMES
%token LEQ LT EQ
%token EOF
/* last tokens have highest precedence */
%start main /* the entry point */
%type <L4_ast.program> main
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
   | LPAREN LET LPAREN LBRACK var exp RBRACK RPAREN exp RPAREN  { LetExp(get_current_pos (), $5, $6, $9) }
   | LPAREN LET LPAREN LPAREN var exp RPAREN RPAREN exp RPAREN  { LetExp(get_current_pos (), $5, $6, $9) }
   | LPAREN IF exp exp exp RPAREN                              { IfExp(get_current_pos (), $3, $4, $5) }
   | LPAREN exp exp_list RPAREN                                 { AppExp(get_current_pos (), $2, $3) }
   | LPAREN NEWARRAY exp exp RPAREN                             { NewArrayExp(get_current_pos (), $3, $4) }
   | LPAREN NEWTUPLE exp_list RPAREN                            { NewTupleExp(get_current_pos (), $3) }
   | LPAREN AREF exp exp RPAREN                                 { ArefExp(get_current_pos (), $3, $4) }
   | LPAREN ASET exp exp exp RPAREN                             { AsetExp(get_current_pos (), $3, $4, $5, true) }
   | LPAREN ALEN exp RPAREN                                     { AlenExp(get_current_pos (), $3) }
   | LPAREN BEGIN exp exp RPAREN                                { BeginExp(get_current_pos (), $3, $4) }
   | LPAREN PRINT exp RPAREN                                    { PrintExp(get_current_pos (), $3) }
   | LPAREN MAKECLOSURE LABEL exp RPAREN                        { MakeClosureExp(get_current_pos (), $3, $4) }
   | LPAREN CLOSUREPROC exp RPAREN                              { ClosureProcExp(get_current_pos (), $3) }
   | LPAREN CLOSUREVARS exp RPAREN                              { ClosureVarsExp(get_current_pos (), $3) }
   | LPAREN PLUS exp exp RPAREN                                 { PlusExp(get_current_pos (), $3, $4) }
   | LPAREN MINUS exp exp RPAREN                                { MinusExp(get_current_pos (), $3, $4) }
   | LPAREN TIMES exp exp RPAREN                                { TimesExp(get_current_pos (), $3, $4) }
   | LPAREN LT exp exp RPAREN                                   { LtExp(get_current_pos (), $3, $4) }
   | LPAREN LEQ exp exp RPAREN                                  { LeqExp(get_current_pos (), $3, $4) }
   | LPAREN EQ exp exp RPAREN                                   { EqExp(get_current_pos (), $3, $4) }
   | LPAREN NUMBERQ exp RPAREN                                  { NumberPredExp(get_current_pos (), $3) }
   | LPAREN ARRAYQ exp RPAREN                                   { ArrayPredExp(get_current_pos (), $3) }
   | var                                                        { VarExp(get_current_pos(), $1) }
   | INT                                                        { IntExp(get_current_pos(), $1) }
   | LABEL                                                      { LabelExp(get_current_pos(), $1) }
;

exp_list:
   |              { [] }
   | exp exp_list { $1::$2 }
;

var:
   | IDENT { Var(get_current_pos (), $1) }
;

var_list:
                  { [] }
   | var var_list { $1::$2 }
;
