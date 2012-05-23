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

target_lang := 3;;

(* program banner text *)
let banner_text = "L4 Compiler v. 1.0\n------------------" in
let in_stream = parse_command_line banner_text in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = L4_parser.main L4_lexer.token lexbuf in (* run the parser, producing AST *)
if !target_lang <= 0 then L1_code.generate_binary (L2_code.compile_program
                                                  (L3_code.compile_program
                                                  (compile_program result))) !binary_file_name
else (
   let out_stream = open_out_file () in
   (if !target_lang <= 1 then L1_ast.output_program out_stream (L2_code.compile_program
                                                               (L3_code.compile_program
                                                               (compile_program result)))
   else if !target_lang <= 2 then L2_ast.output_program out_stream (L3_code.compile_program
                                                                   (compile_program result))
   else if !target_lang <= 3 then L3_ast.output_program out_stream (compile_program result)
   else output_program out_stream result);
   output_string out_stream "\n";
   let _ = close_out_file out_stream in ()
);
exit 0
