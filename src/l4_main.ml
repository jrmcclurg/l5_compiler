(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/14/2012
 *
 * L4-to-L3 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l4_main.ml
 *)

open L4_ast;;
open L4_code;;
open Utils;;
open Flags;;

(* program banner text *)
let banner_text = "L4 Compiler v. 1.0\n------------------" in
let in_stream = parse_command_line banner_text in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = L4_parser.main L4_lexer.token lexbuf in (* run the parser, producing AST *)
(* if we only need to print the parsed L1 code, do so *)
let p3 = compile_program result in      (* compile from L4 to L3 *)
let p2 = L3_code.compile_program p3 in  (* compile from L3 to L2 *)
let p1 = L2_code.compile_program p2 in  (* compile from L2 to L1 *)
if !target_lang <= 0 then L1_code.generate_binary p1 !binary_file_name
else (
   let out_stream = open_out_file () in
   (if !target_lang <= 1 then L1_ast.output_program out_stream p1
   else if !target_lang <= 2 then L2_ast.output_program out_stream p2
   else if !target_lang <= 3 then L3_ast.output_program out_stream p3
   else output_program out_stream result);
   output_string out_stream "\n";
   let _ = close_out_file out_stream in ()
);
exit 0
