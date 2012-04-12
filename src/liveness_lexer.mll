(*
 * EECS 322 Compiler Construction 
 * Northwestern University
 * 4/16/2012
 *
 * Liveness Test
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * liveness_lexer.mll
 * This is the lexer specification for the Liveness Test,
 * to be used with ocamllex.
 *)

{
   open Liveness_parser;; (* The type token is defined in liveness_parser.mli *)
   open L2_ast;;
   open Utils;;
}
rule token = parse
  [' ' '\t']                 { token lexbuf }                     (* skip blanks *)
| ['\r']                     { token lexbuf }                    (* skip blanks *)
| ['\n']                     { do_newline lexbuf; token lexbuf } (* skip newlines (but count them) *)
| (['-']? ['0'-'9']+) as s   { let i = Int64.of_string s in
                               check_int_range i;
                               INT(Int64.of_string s) }          (* pos/neg integers *)
| "array-error"              { ARRAYERR }                        (* keywords *)
| "tail-call"                { TAILCALL }
| "allocate"                 { ALLOC }
| "return"                   { RETURN }
| "print"                    { PRINT }
| "cjump"                    { CJUMP }
| "goto"                     { GOTO }
| "mem"                      { MEM }
| "call"                     { CALL }
| "esi"                      { ESI }                             (* named registers *)
| "edi"                      { EDI }
| "ebp"                      { EBP }
| "esp"                      { ESP }
| "eax"                      { EAX }
| "ecx"                      { ECX }
| "edx"                      { EDX }
| "ebx"                      { EBX }
| '('                        { LPAREN }                          (* parentheses *)
| ')'                        { RPAREN }
| "+="                       { PLUSEQ }                          (* arithmetic operators *)
| "-="                       { MINUSEQ }
| "*="                       { TIMESEQ }
| "&="                       { BITANDEQ }
| "<<="                      { SLLEQ }                           (* shift operators *)
| ">>="                      { SRLEQ }
| "<-"                       { GETS }                            (* register assignment *)
| "<="                       { LEQ }                             (* comparison operators *)
| "<"                        { LT }
| "="                        { EQ }
| ';' [^'\n']*               { token lexbuf }                    (* single-line comment *)
| ':' (['a'-'z' 'A'-'Z' '_']
      ['a'-'z' 'A'-'Z'
       '0'-'9' '_']* as s)   { LABEL(s) }                        (* label *)
| ['a'-'z' 'A'-'Z' '-'
   '_' '0'-'9']* as s        { IDENT(s) }                        (* variable *)
| eof { EOF }
| _ { let p = Lexing.lexeme_end_p lexbuf in
      let file_name = p.Lexing.pos_fname in
      let line_num = p.Lexing.pos_lnum in
      let col_num = (p.Lexing.pos_cnum-p.Lexing.pos_bol) in
      print_string ("Lexical error in '"^file_name^
   "' on line "^(string_of_int line_num)^" col "^(string_of_int
   col_num)^"!\n"); raise Lexing_error }
