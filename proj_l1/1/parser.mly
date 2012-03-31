/* File parser.mly */
%{
   open Ast;;
   open Utils;;
%}
%token <int> INT
%token <string> LABEL
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
%type <Ast.program> main
%%
main:
   LPAREN func func_list RPAREN { Program(get_current_pos (), $2::$3) }
   /* NOTE XXX - at some point, add EOF here */
;

func:
   | LPAREN instr instr_list RPAREN {
      (* we need to see if this function has a name *)
      (* (using a separate rule for the labeled functions
       *  causes a shift/reduce conflict in the parser) *)
      let il = $2::$3 in
      let a = List.hd il in
      let ax = List.tl il in
      let (name,l) =
      (match a with
      | LabelInstr(_,s) -> (Some(s),ax)
      | _ -> (None,il)) in
      Function(get_current_pos (), name, l)
   }
;

func_list:
                   { [] }
  | func func_list { $1::$2 }
;

instr:
   | LPAREN reg GETS sval RPAREN                             { AssignInstr(get_current_pos (), $2, $4) }
   | LPAREN reg GETS LPAREN MEM reg INT RPAREN RPAREN        { MemReadInstr(get_current_pos (), $2, $6, $7) }
   | LPAREN LPAREN MEM reg INT RPAREN GETS sval RPAREN       { MemWriteInstr(get_current_pos (), $4, $5, $8) }

   | LPAREN reg PLUSEQ tval RPAREN                           { PlusInstr(get_current_pos (), $2, $4) }
   | LPAREN reg MINUSEQ tval RPAREN                          { MinusInstr(get_current_pos (), $2, $4) }
   | LPAREN reg TIMESEQ tval RPAREN                          { TimesInstr(get_current_pos (), $2, $4) }
   | LPAREN reg BITANDEQ tval RPAREN                         { BitAndInstr(get_current_pos (), $2, $4) }
   | LPAREN reg SLLEQ sreg RPAREN                           { SllInstr(get_current_pos (), $2, $4) }
   | LPAREN reg SRLEQ sreg RPAREN                           { SrlInstr(get_current_pos (), $2, $4) }
   /* the "reg" in the following three lines gets parsed as creg */
   | LPAREN reg GETS tval LT tval RPAREN                     { LtInstr(get_current_pos (), get_creg $2, $4, $6) }
   | LPAREN reg GETS tval LEQ tval RPAREN                    { LeqInstr(get_current_pos (), get_creg $2, $4, $6) }
   | LPAREN reg GETS tval EQ tval RPAREN                     { EqInstr(get_current_pos (), get_creg $2, $4, $6) }
   | LABEL                                                   { LabelInstr(get_current_pos (), $1) }
   | LPAREN GOTO LABEL RPAREN                                { GotoInstr(get_current_pos (), $3) }
   | LPAREN CJUMP tval LT tval LABEL LABEL RPAREN            { LtJumpInstr(get_current_pos (), $3, $5, $6, $7) }
   | LPAREN CJUMP tval LEQ tval LABEL LABEL RPAREN           { LeqJumpInstr(get_current_pos (), $3, $5, $6, $7) }
   | LPAREN CJUMP tval EQ tval LABEL LABEL RPAREN            { EqJumpInstr(get_current_pos (), $3, $5, $6, $7) }
   | LPAREN CALL uval RPAREN                                 { CallInstr(get_current_pos (), $3) }
   | LPAREN TAILCALL uval RPAREN                             { TailCallInstr(get_current_pos (), $3) }
   | LPAREN RETURN RPAREN                                    { ReturnInstr(get_current_pos ()) }
   /* the "reg" in the following three rules gets parsed as eax */
   | LPAREN reg GETS LPAREN PRINT tval RPAREN RPAREN         { let r = $2 in
                                                               (match r with
                                                                | CallerSaveReg(_,EaxReg(_)) -> ()
                                                                | _ -> parse_error "Destination must be EAX");
                                                               PrintInstr(get_current_pos (), $6) }
   | LPAREN reg GETS LPAREN ALLOC tval tval RPAREN RPAREN    { let r = $2 in
                                                               (match r with
                                                                | CallerSaveReg(_,EaxReg(_)) -> ()
                                                                | _ -> parse_error "Destination must be EAX");
                                                               AllocInstr(get_current_pos (), $6, $7) }
   | LPAREN reg GETS LPAREN ARRAYERR tval tval RPAREN RPAREN { let r = $2 in
                                                               (match r with
                                                                | CallerSaveReg(_,EaxReg(_)) -> ()
                                                                | _ -> parse_error "Destination must be EAX");
                                                               ArrayErrorInstr(get_current_pos (), $6, $7) }
;

instr_list:
                   { [] }
  | instr instr_list { $1::$2 }
;

reg:
   | ESI { EsiReg(get_current_pos ()) }
   | EDI { EdiReg(get_current_pos ()) }
   | EBP { EbpReg(get_current_pos ()) }
   | ESP { EspReg(get_current_pos ()) }
   | EAX { CallerSaveReg(get_current_pos (), EaxReg(get_current_pos ())) }
   | ECX { CallerSaveReg(get_current_pos (), EcxReg(get_current_pos ())) }
   | EDX { CallerSaveReg(get_current_pos (), EdxReg(get_current_pos ())) }
   | EBX { CallerSaveReg(get_current_pos (), EbxReg(get_current_pos ())) }
;

sreg:
   | ECX { EcxShReg(get_current_pos ()) }
   | INT { IntShVal(get_current_pos (), $1) }
;

sval:
   | reg  { RegSVal(get_current_pos(), $1) }
   | INT   { IntSVal(get_current_pos(), $1) }
   | LABEL { LabelSVal(get_current_pos(), $1) }
;

uval:
   | reg  { RegUVal(get_current_pos(), $1) }
   | LABEL { LabelUVal(get_current_pos(), $1) }
;

tval:
   | reg  { RegTVal(get_current_pos(), $1) }
   | INT   { IntTVal(get_current_pos(), $1) }
;
