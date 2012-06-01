(*
 * EECS 322 Compiler Construction 
 * Northwestern University
 * 4/9/2012
 *
 * Spill Test
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * spill_lexer.mll
 * This is the lexer specification for the Spill Test,
 * to be used with ocamllex.
 *)

{
   open Spill_parser;; (* The type token is defined in spill_parser.mli *)
   open L2_ast;;
   open Utils;;
}
rule token = parse
  [' ' '\t']                 { token lexbuf }                    (* skip blanks *)
| ['\r']                     { token lexbuf }                    (* skip blanks *)
| ['\n']                     { do_newline lexbuf; token lexbuf } (* skip newlines (but count them) *)
| (['-']? ['0'-'9']+) as s   { let i = Int32.of_string s in
                               check_int_range i;
                               INT(Int32.of_string s) }          (* pos/neg integers *)
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
       '0'-'9' '_']* as s)   { let id = add_symbol s in
                               LABEL(id) }                       (* label *)
| ['a'-'z' 'A'-'Z' '-'
   '_' '0'-'9']* as s        { let id = add_symbol s in
                               IDENT(id) }                       (* variable *)
| eof { EOF }
| _ { lex_error "Lexing error" lexbuf }
