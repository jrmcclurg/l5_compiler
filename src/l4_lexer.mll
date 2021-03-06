(*
 * EECS 322 Compiler Construction 
 * Northwestern University
 * 5/14/2012
 *
 * L4-to-L3 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l4_lexer.mll
 * This is the lexer specification for the L4 language,
 * to be used with ocamllex.
 *)

{
   open L4_parser;; (* The type token is defined in parser.mli *)
   open L4_ast;;
   open Utils;;
}
rule token = parse
  [' ' '\t']                 { token lexbuf }                    (* skip blanks *)
| ['\r']                     { token lexbuf }                    (* skip blanks *)
| ['\n']                     { do_newline lexbuf; token lexbuf } (* skip newlines (but count them) *)
| (['-']? ['0'-'9']+) as s   { let i = Int32.of_string s in
                               check_int_range i;
                               INT(Int32.of_string s) }          (* pos/neg integers *)
| "closure-proc"             { CLOSUREPROC }                     (* functions *)
| "closure-vars"             { CLOSUREVARS }
| "make-closure"             { MAKECLOSURE }
| "new-array"                { NEWARRAY }
| "new-tuple"                { NEWTUPLE }
| "print"                    { PRINT }
| "begin"                    { BEGIN }
| "aset"                     { ASET }
| "aref"                     { AREF }
| "alen"                     { ALEN }
| "let"                      { LET }                             (* keywords *)
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
| ':' (['a'-'z' 'A'-'Z' '_']
      ['a'-'z' 'A'-'Z'
       '0'-'9' '_']* as s)   { let id = add_symbol s in
                               LABEL(id) }                        (* label *)
| ['a'-'z' 'A'-'Z' '-'
   '_' '0'-'9']* as s        { let id = add_symbol s in
                               IDENT(id) }                        (* variable *)
| eof { EOF }
| _ { lex_error "Lexing error" lexbuf }
