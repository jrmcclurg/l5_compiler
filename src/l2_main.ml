(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/9/2012
 *
 * L2-to-L1 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l2_main.ml
 * In progress!!!! Currently just prints the parsed L2 program.
 *)

open L2_ast;;
open Utils;;

(* flags and defaults for command-line args *)
let assembly_file_name = ref "prog.S";;
let runtime_file_name  = ref "runtime.c";;
let output_file_name   = ref "a.out";;
let use_32bit_arch     = ref true;;
let do_print_only      = ref true;;
let verbose_mode       = ref false;;

(* program banner text *)
let banner_text = "L2 Compiler v. 1.0\n------------------";;

(* parse the command-line arguments *)
let filename = ref "";;
Arg.parse [
] (fun x -> filename := x) banner_text;;

(* use the command-line filename if one exists, otherwise use stdin *)
let in_stream = if (!filename="") then stdin else (
   try (open_in !filename)
   with _ -> die_system_error ("can't read from file: "^
      (Sys.getcwd ())^"/"^(!filename))
) in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = L2_parser.main L2_lexer.token lexbuf in (* run the parser, producing AST *)
(* if we only need to print the parsed L1 code, do so *)
if !do_print_only then (
   print_program result;
   print_newline()
);
exit 0
