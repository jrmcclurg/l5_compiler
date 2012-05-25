/*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/16/2012
 *
 * Liveness Test
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * liveness_parser.mly
 * This is the specification for the Liveness Test parser, to be
 * used with ocamlyacc.
 */
%{
   open L2_ast;;
   open Utils;;
%}
%token <int64> INT
%token <int> LABEL
%token <int> IDENT 
%token ARRAYERR TAILCALL ALLOC RETURN PRINT CJUMP GOTO MEM CALL
%token ESI EDI EBP ESP
%token EAX ECX EDX EBX
%token LPAREN RPAREN
%token PLUSEQ MINUSEQ TIMESEQ BITANDEQ
%token SLLEQ SRLEQ
%token GETS 
%token LEQ LT EQ
%token EOF
/* last tokens have highest precedence */
%start main /* the entry point */
%type <L2_ast.instr list> main
%%
main:
   LPAREN instr_list RPAREN { $2 }
                              /* TODO XXX - these will be var ids (use symbol table) */
   /* TODO XXX - add the EOF at some point */
;

instr:
   | LPAREN var GETS sval RPAREN                             { AssignInstr(get_current_pos (), $2, $4) }
   | LPAREN var GETS LPAREN MEM var INT RPAREN RPAREN        { let i = $7 in
                                                               check_int_alignment i;
                                                               MemReadInstr(get_current_pos (), $2, $6, i) }
   | LPAREN LPAREN MEM var INT RPAREN GETS sval RPAREN       { let i = $5 in
                                                               check_int_alignment i;
                                                               MemWriteInstr(get_current_pos (), $4, i, $8) }
   | LPAREN var PLUSEQ tval RPAREN                           { PlusInstr(get_current_pos (), $2, $4) }
   | LPAREN var MINUSEQ tval RPAREN                          { MinusInstr(get_current_pos (), $2, $4) }
   | LPAREN var TIMESEQ tval RPAREN                          { TimesInstr(get_current_pos (), $2, $4) }
   | LPAREN var BITANDEQ tval RPAREN                         { BitAndInstr(get_current_pos (), $2, $4) }
   | LPAREN var SLLEQ svar RPAREN                            { SllInstr(get_current_pos (), $2, $4) }
   | LPAREN var SRLEQ svar RPAREN                            { SrlInstr(get_current_pos (), $2, $4) }
   | LPAREN var GETS tval LT tval RPAREN                     { LtInstr(get_current_pos (), $2, $4, $6) }
   | LPAREN var GETS tval LEQ tval RPAREN                    { LeqInstr(get_current_pos (), $2, $4, $6) }
   | LPAREN var GETS tval EQ tval RPAREN                     { EqInstr(get_current_pos (), $2, $4, $6) }
   | LABEL                                                   { LabelInstr(get_current_pos (), $1) }
   | LPAREN GOTO LABEL RPAREN                                { GotoInstr(get_current_pos (), $3) }
   | LPAREN CJUMP tval LT tval LABEL LABEL RPAREN            { LtJumpInstr(get_current_pos (), $3, $5, $6, $7) }
   | LPAREN CJUMP tval LEQ tval LABEL LABEL RPAREN           { LeqJumpInstr(get_current_pos (), $3, $5, $6, $7) }
   | LPAREN CJUMP tval EQ tval LABEL LABEL RPAREN            { EqJumpInstr(get_current_pos (), $3, $5, $6, $7) }
   | LPAREN CALL uval RPAREN                                 { CallInstr(get_current_pos (), $3) }
   | LPAREN TAILCALL uval RPAREN                             { TailCallInstr(get_current_pos (), $3) }
   | LPAREN RETURN RPAREN                                    { ReturnInstr(get_current_pos ()) }
   /* the "var" in the following three rules gets parsed as eax */
   | LPAREN var GETS LPAREN PRINT tval RPAREN RPAREN         { let r = $2 in
                                                               (match r with
                                                                | VarOrReg(_,id,_) -> if id == eax_id then ()
                                                                else parse_error "destination must be eax");
                                                               PrintInstr(get_current_pos (), $6) }
   | LPAREN var GETS LPAREN ALLOC tval tval RPAREN RPAREN    { let r = $2 in
                                                               (match r with
                                                                | VarOrReg(_,id,_) -> if id == eax_id then ()
                                                                else parse_error "destination must be eax");
                                                               AllocInstr(get_current_pos (), $6, $7) }
   | LPAREN var GETS LPAREN ARRAYERR tval tval RPAREN RPAREN { let r = $2 in
                                                               (match r with
                                                                | VarOrReg(_,id,_) -> if id == eax_id then ()
                                                                | _ -> parse_error "destination must be eax");
                                                               ArrayErrorInstr(get_current_pos (), $6, $7) }
;

instr_list:
                     { [] }
  | instr instr_list { $1::$2 }
;

var:
   | ESI { VarOrReg(get_current_pos (), esi_id, false) }
   | EDI { VarOrReg(get_current_pos (), edi_id, false) }
   | EBP { VarOrReg(get_current_pos (), ebp_id, false) }
   | ESP { VarOrReg(get_current_pos (), esp_id, false) }
   | EAX { VarOrReg(get_current_pos (), eax_id, false) }
   | ECX { VarOrReg(get_current_pos (), ecx_id, false) }
   | EDX { VarOrReg(get_current_pos (), edx_id, false) }
   | EBX { VarOrReg(get_current_pos (), ebx_id, false) }
   | IDENT { VarOrReg(get_current_pos (), $1, true)}
;

svar:
   | INT { IntShVal(get_current_pos (), $1) }
   | var { ShVar(get_current_pos (), $1) }
;

sval:
   | var  { VarSVal(get_current_pos(), $1) }
   | INT   { IntSVal(get_current_pos(), $1) }
   | LABEL { LabelSVal(get_current_pos(), $1) }
;

uval:
   | var  { VarUVal(get_current_pos(), $1) }
   | INT   { IntUVal(get_current_pos(), $1) }
   | LABEL { LabelUVal(get_current_pos(), $1) }
;

tval:
   | var  { VarTVal(get_current_pos(), $1) }
   | INT   { IntTVal(get_current_pos(), $1) }
   | LABEL { LabelTVal(get_current_pos(), $1) }
;
