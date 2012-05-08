(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/7/2012
 *
 * L3-to-L2 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l3_main.ml
 *)

open L3_ast;;
open L3_code;;
open Utils;;

(* flags and defaults for command-line args *)
let assembly_file_name = ref "prog.S";;
let runtime_file_name  = ref "runtime.c";;
let output_file_name   = ref "a.out";;
let do_print_only      = ref false;;
let verbose_mode       = ref false;;
let do_compile         = ref false;;

(* program banner text *)
let banner_text = "L3 Compiler v. 1.0\n------------------";;

(* parse the command-line arguments *)
let filename = ref "";;
Arg.parse [
("-v",        Arg.Unit(fun x -> verbose_mode := true),
                    "Turn on verbose output");
   ("-parse",    Arg.Unit(fun x -> do_print_only := true),
                    "Print the parsed L1 code and exit");
   ("-o",        Arg.String(fun x -> output_file_name := x; do_compile := true),
                    "Location of the compiled result (default: a.out)")
] (fun x -> filename := x) banner_text;;

(* use the command-line filename if one exists, otherwise use stdin *)
let in_stream = if (!filename="") then stdin else (
   try (open_in !filename)
   with _ -> die_system_error ("can't read from file: "^
      (Sys.getcwd ())^"/"^(!filename))
) in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = L3_parser.main L3_lexer.token lexbuf in (* run the parser, producing AST *)
(* if we only need to print the parsed L1 code, do so *)
if !do_print_only then (
   print_program result;
   print_newline()
) else if !do_compile then (
   let p2 = compile_program result in     (* compile from L3 to L2 *)
   let p1 = L2_code.compile_program p2 in (* compile from L2 to L1 *)
   (* generate the C runtime *)
   let out1 = (try (open_out !runtime_file_name)
      with _ -> die_system_error ("can't write to file: "^
         (Sys.getcwd ())^"/"^(!runtime_file_name))
   ) in
   L1_code.generate_runtime out1;
   close_out out1;
   (* generate the assembly code *)
   let out2 = (try (open_out !assembly_file_name)
      with _ -> die_system_error ("can't write to file: "^
      (Sys.getcwd ())^"/"^(!assembly_file_name))
   ) in
   L1_code.compile_program out2 p1;
   close_out out2;
   (* compile and link everything *)
   L1_code.compile_and_link !output_file_name !assembly_file_name true
) else (
   let p = compile_program result in
   L2_ast.print_program p
);
exit 0
