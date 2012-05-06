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
%token <int64> INT
%token <string> LABEL
%token <string> IDENT 
%token CLOSUREPROC CLOSUREVARS MAKECLOSURE NEWARRAY NEWTUPLE PRINT
%token ASET AREF ALEN
%token LET IF
%token LPAREN RPAREN LBRACK RBRACK
%token PLUS MINUS TIMES
%token QUESTION
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
   | LPAREN IF sval exp exp RPAREN                              { IfExp(get_current_pos (), $3, $4, $5) }
   | dexp                                                       { DExpExp(get_current_pos (), $1) }
;

dexp:
   | LPAREN biop sval sval RPAREN          { BiopDExp(get_current_pos (), $2, $3, $4) }
   | LPAREN pred sval RPAREN               { PredDExp(get_current_pos (), $2, $3) }
   | LPAREN sval sval_list RPAREN          { AppDExp(get_current_pos (), $2, $3) (* TODO - can the parens be empty? *) }
   | LPAREN NEWARRAY sval sval RPAREN      { NewArrayDExp(get_current_pos (), $3, $4) }
   | LPAREN NEWTUPLE sval sval_list RPAREN { NewTupleDExp(get_current_pos (), $3::$4) }
   | LPAREN AREF sval sval RPAREN          { ArefDExp(get_current_pos (), $3, $4) }
   | LPAREN ASET sval sval RPAREN          { AsetDExp(get_current_pos (), $3, $4) }
   | LPAREN ALEN sval sval RPAREN          { AlenDExp(get_current_pos (), $3, $4) }
   | LPAREN PRINT sval RPAREN              { PrintDExp(get_current_pos (), $3) }
   | LPAREN MAKECLOSURE LABEL sval RPAREN  { MakeClosureDExp(get_current_pos (), $3, $4) }
   | LPAREN CLOSUREPROC sval RPAREN        { ClosureProcDExp(get_current_pos (), $3) }
   | LPAREN CLOSUREVARS sval RPAREN        { ClosureVarsDExp(get_current_pos (), $3) }
   | sval                                  { SValDExp(get_current_pos (), $1) }

var:
   | IDENT {
      let raw = $1 in
      (* TODO - put this somewhere more accessible? *)
      let regs = ["esi";"edi";"ebp";"esp";"eax";"ecx";"edx";"ebx";
                  "array-error";"tail-call";"allocate";"return";"cjump";"goto";"mem";"call"] in
      let name = (try (l3_prefix^(List.find (fun x -> (x = raw)) regs))
                  with _ -> raw) in
      Var(get_current_pos (), name)}
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

biop:
   | PLUS  { PlusBiop(get_current_pos ()) }
   | MINUS { MinusBiop(get_current_pos ()) }
   | TIMES { TimesBiop(get_current_pos ()) }
   | LT    { LtBiop(get_current_pos ()) }
   | LEQ   { LeqBiop(get_current_pos ()) }
   | EQ    { EqBiop(get_current_pos ()) }
;

pred:
   | INT QUESTION { NumberPred(get_current_pos (), $1) }
   | var QUESTION { VarPred(get_current_pos (), $1) }
