(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/3/2012
 *
 * L1-to-assembly Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * main.ml
 * This is the entry-point for the L1 compiler.
 * It parses the specified L1 file, generates
 * code via the functionality in code.ml, and
 * compiles/links everything via gcc/as.
 *)

open L1_ast;;
open L1_code;;
open Utils;;
open Flags;;

target_lang := 0;;

(* program banner text *)
let banner_text = "L1 Compiler v. 1.0\n------------------" in
(* parse the command-line arguments *)
let in_stream = parse_command_line banner_text in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = L1_parser.main L1_lexer.token lexbuf in (* run the parser, producing AST *)
if !target_lang <= 0 then generate_binary result !binary_file_name
else (
   let out_stream = open_out_file () in
   output_program out_stream result;
   output_string out_stream "\n";
   let _ = close_out_file out_stream in ()
);
exit 0
