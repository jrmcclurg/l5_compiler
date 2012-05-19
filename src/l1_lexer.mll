(*
 * EECS 322 Compiler Construction 
 * Northwestern University
 * 4/3/2012
 *
 * L1-to-assembly Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * lexer.mll
 * This is the lexer specification for the L1 language,
 * to be used with ocamllex.
 *)

{
   open L1_parser;; (* The type token is defined in parser.mli *)
   open L1_ast;;
   open Utils;;
}
rule token = parse
  [' ' '\t']                 {token lexbuf }                     (* skip blanks *)
| ['\r']                     { token lexbuf }                    (* skip blanks *)
| ['\n']                     { do_newline lexbuf; token lexbuf } (* skip newlines (but count them) *)
| (['-']? ['0'-'9']+) as s   { let i = Int64.of_string s in
                               check_int_range i;
                               INT(Int64.of_string s) }          (* pos/neg integers *)
| "print-string"             { PRINTSTR }                        (* keywords *)
| "array-error"              { ARRAYERR }
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
| '"' ([^ '"']*) '"' as s    { let s2 = Scanf.sscanf s "%S" (fun x -> x) in
                               STRING(s2) }
| eof { EOF }
| _ { lex_error "Lexing error" lexbuf }
