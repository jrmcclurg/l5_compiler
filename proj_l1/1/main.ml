let assembly_file_name = "prog.S";;
let runtime_file_name  = "runtime.c";;

let filename = ref "";;
Arg.parse [] (fun x -> filename := x) "L1 Compiler v. 1.0\nby Jedidiah McClurg";;

let in_stream = if (!filename="") then stdin else (open_in !filename) in
let lexbuf = Lexing.from_channel in_stream in
let result = Parser.main Lexer.token lexbuf in
(*Ast.print_program result;
print_newline();*)
let out1 = (open_out runtime_file_name) in
Code.generate_runtime out1;
close_out out1;
let out2 = (open_out assembly_file_name) in
Code.compile_program out2 result;
close_out out2;
Code.compile_assembly ();
(*print_string "\nDone";
print_newline();*)
exit 0
