let filename = ref "";;
Arg.parse [] (fun x -> filename := x) "Parser Generator Generator v. 1.0\nby Jedidiah McClurg";;

let in_stream = if (!filename="") then stdin else (open_in !filename) in
let lexbuf = Lexing.from_channel in_stream in
let result = Parser.main Lexer.token lexbuf in
(* Ast.print_grammar 0 result;
print_newline(); *)
Code.generate_code !filename result;
print_string "\nDone";
print_newline();
exit 0
