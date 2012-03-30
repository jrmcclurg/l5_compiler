{
   open Parser;; (* The type token is defined in parser.mli *)
   open Ast;;
   open Utils;;
}
rule token = parse
  [' ' '\t'] {token lexbuf } (* skip blanks *)
| ['\r'] { token lexbuf } (* skip blanks *)
| ['\n'] { do_newline lexbuf; token lexbuf }
| ['0'-'9']+ as s { INT(int_of_string s) }
| "eof" { ENDFILE }
| "left" { LEFT }
| "right" { RIGHT }
| "unary" { UNARY }
| '/' '/' [^'\n']* { token lexbuf }
| ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']* as s { IDENT(s) }
| '{' { let p = Lexing.lexeme_start_p lexbuf in
        let s = code 0 "" lexbuf in
        CODE(p, Some(s)) }
| "/*" { comment 0 lexbuf }
| '[' (([^'\\' ']']* ('\\' _)*)* as s) ']' { CHARSET(Ast.string_of_string ("\""^s^"\"")) }
| '"' (([^'\\' '"']* ('\\' _)*)*) '"' as s { STRINGQUOT(Ast.string_of_string s) }
| '\'' (([^'\\' '\''] |
         ('\\' ('\\'|'"'|'\''|'n'|'r'|'t'|'b')) |
         ('\\' ['0'-'9'] ['0'-'9'] ['0'-'9']) )) '\'' as s { CHARQUOT(Ast.char_of_string s) }
| '-' '>' { ARROW }
| '|' { BAR }
| ';' { SEMI }
| ':' { COLON }
| '*' { STAR }
| '+' { PLUS }
| '?' { QUESTION }
| '_' { WILDCARD }
| '\\' { DIFF }
| '{' { LBRACK }
| '}' { RBRACK }
| '(' { LPAREN }
| ')' { RPAREN }
| ".." { RANGE }
| eof { EOF }
| _ { let p = Lexing.lexeme_end_p lexbuf in
      let file_name = p.Lexing.pos_fname in
      let line_num = p.Lexing.pos_lnum in
      let col_num = (p.Lexing.pos_cnum-p.Lexing.pos_bol) in
      print_string ("Lexical error in '"^file_name^
   "' on line "^(string_of_int line_num)^" col "^(string_of_int
   col_num)^"!\n"); raise Lexing_error }

and code n s = parse
| '{' { code (n+1) (s^"{") lexbuf }
| '}' { if (n=0) then s else code (n-1) (s^"}") lexbuf }
| _ as c { if c='\n' then do_newline lexbuf;
           code n (Printf.sprintf "%s%c" s c) lexbuf }

and comment n = parse
| "/*" { comment (n+1) lexbuf }
| "*/" { if (n=0) then token lexbuf else comment (n-1) lexbuf }
| _ as c { if c='\n' then do_newline lexbuf;
           comment n lexbuf }
