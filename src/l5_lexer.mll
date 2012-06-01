(*
 * EECS 322 Compiler Construction 
 * Northwestern University
 * 5/21/2012
 *
 * L5-to-L4 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l5_lexer.mll
 * This is the lexer specification for the L5 language,
 * to be used with ocamllex.
 *)

{
   open L5_parser;; (* The type token is defined in l5_parser.mli *)
   open L5_ast;;
   open Utils;;
}
rule token = parse
  [' ' '\t']                 { token lexbuf }                    (* skip blanks *)
| ['\r']                     { token lexbuf }                    (* skip blanks *)
| ['\n']                     { do_newline lexbuf; token lexbuf } (* skip newlines (but count them) *)
| (['-']? ['0'-'9']+) as s   { let i = Int32.of_string s in
                               check_int_range i;
                               INT(Int32.of_string s) }          (* pos/neg integers *)
| "new-array"                { NEWARRAY }                        (* functions *)
| "new-tuple"                { NEWTUPLE }
| "letrec"                   { LETREC }
| "print"                    { PRINT }
| "begin"                    { BEGIN }
| "aset"                     { ASET }
| "aref"                     { AREF }
| "alen"                     { ALEN }
| "lambda"                   { LAMBDA }                          (* keywords *)
| "let"                      { LET }
| "if"                       { IF }
| "number?"                  { NUMBERQ }                         (* predicates *)
| "a?"                       { ARRAYQ }
| '('                        { LPAREN }                          (* parentheses *)
| ')'                        { RPAREN }
| '['                        { LBRACK }                          (* brackets *)
| ']'                        { RBRACK }
| "+"                        { PLUS }                            (* arithmetic operators *)
| "-"                        { MINUS }
| "*"                        { TIMES }
| "<="                       { LEQ }                             (* comparison operators *)
| "<"                        { LT }
| "="                        { EQ }
| ';' [^'\n']*               { token lexbuf }                    (* single-line comment *)
| ['a'-'z' 'A'-'Z' '-'
   '_' '0'-'9']* as s        { let id = add_symbol s in
                               IDENT(id) }                       (* variable *)
| eof { EOF }
| _ { lex_error "Lexing error" lexbuf }
