/*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/21/2012
 *
 * L5-to-L4 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l5_parser.mly
 * This is the specification for the L5 parser, to be
 * used with ocamlyacc.
 */
%{
   open L5_ast;;
   open Utils;;
%}
%token <int64> INT
%token <string> IDENT 
%token NEWARRAY NEWTUPLE PRINT
%token ASET AREF ALEN NUMBERQ ARRAYQ BEGIN
%token LET IF LETREC LAMBDA
%token LPAREN RPAREN LBRACK RBRACK
%token PLUS MINUS TIMES
%token LEQ LT EQ
%token EOF
/* last tokens have highest precedence */
%start main /* the entry point */
%type <L5_ast.program> main
%%
main:
   exp { Program(get_current_pos (), $1) }
   /* TODO XXX - add EOF here at some point */ 
;

exp:
   | LPAREN LAMBDA LPAREN var_list RPAREN exp RPAREN              { LambdaExp(get_current_pos (), $4, $6) }
   | var                                                          { VarExp(get_current_pos(), $1) }
   | LPAREN LET LPAREN LBRACK var exp RBRACK RPAREN exp RPAREN    { LetExp(get_current_pos (), $5, $6, $9) }
   | LPAREN LET LPAREN LPAREN var exp RPAREN RPAREN exp RPAREN    { LetExp(get_current_pos (), $5, $6, $9) }
   | LPAREN LETREC LPAREN LBRACK var exp RBRACK RPAREN exp RPAREN { LetRecExp(get_current_pos (), $5, $6, $9) }
   | LPAREN LETREC LPAREN LPAREN var exp RPAREN RPAREN exp RPAREN { LetRecExp(get_current_pos (), $5, $6, $9) }
   | LPAREN IF exp exp exp RPAREN                                 { IfExp(get_current_pos (), $3, $4, $5) }
   | LPAREN NEWTUPLE exp_list RPAREN                              { NewTupleExp(get_current_pos (), $3) }
   | LPAREN BEGIN exp exp RPAREN                                  { BeginExp(get_current_pos (), $3, $4) }
   | LPAREN exp exp_list RPAREN                                   { AppExp(get_current_pos (), $2, $3) }
   | prim                                                         { PrimExp(get_current_pos (), $1) }
   | INT                                                          { IntExp(get_current_pos(), $1) }
;

prim:
   | PLUS     { PlusPrim(get_current_pos ()) }
   | MINUS    { MinusPrim(get_current_pos ()) }
   | TIMES    { TimesPrim(get_current_pos ()) }
   | LT       { LtPrim(get_current_pos ()) }
   | LEQ      { LeqPrim(get_current_pos ()) }
   | EQ       { EqPrim(get_current_pos ()) }
   | NUMBERQ  { NumberPredPrim(get_current_pos ()) }
   | ARRAYQ   { ArrayPredPrim(get_current_pos ()) }
   | PRINT    { PrintPrim(get_current_pos ()) }
   | NEWARRAY { NewArrayPrim(get_current_pos ()) }
   | AREF     { ArefPrim(get_current_pos ()) }
   | ASET     { AsetPrim(get_current_pos ()) }
   | ALEN     { AlenPrim(get_current_pos ()) }

exp_list:
   |              { [] }
   | exp exp_list { $1::$2 }
;

var:
   | IDENT { update_max_ident $1; Var(get_current_pos (), $1) }
;

var_list:
                  { [] }
   | var var_list { $1::$2 }
;
