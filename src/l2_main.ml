(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/26/2012
 *
 * L2-to-L1 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l2_main.ml
 *)

open L2_ast;;
open L2_code;;
open Utils;;
open Flags;;

target_lang   := 1;;

(* program banner text *)
let banner_text = "L2 Compiler v. 1.0\n------------------" in
let in_stream = parse_command_line banner_text in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = L2_parser.main L2_lexer.token lexbuf in (* run the parser, producing AST *)
let p1 = L2_code.compile_program result in (* compile from L2 to L1 *)
if !target_lang <= 0 then L1_code.generate_binary p1 !binary_file_name
else (
   let out_stream = open_out_file () in
   (if !target_lang <= 1 then L1_ast.output_program out_stream p1
   else output_program out_stream result);
   output_string out_stream "\n";
   let _ = close_out_file out_stream in ()
);
exit 0
