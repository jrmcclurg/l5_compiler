(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/16/2012
 *
 * Liveness Test
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * liveness_main.ml
 * This is the entry point for the Liveness Test program.
 *)

open L2_ast;;
open L2_code;;
open Utils;;

(* program banner text *)
let banner_text = "Liveness Test v. 1.0\n------------------";;

(* parse the command-line arguments *)
let filename = ref "";;
Arg.parse [
] (fun x -> filename := x) banner_text;;

let print_instr_list il =
   print_string "(";
   List.iter (fun i -> print_instr i; print_string "\n") il;
   print_string ")\n"
;;

(* use the command-line filename if one exists, otherwise use stdin *)
let in_stream = if (!filename="") then stdin else (
   try (open_in !filename)
   with _ -> die_system_error ("can't read from file: "^
      (Sys.getcwd ())^"/"^(!filename))
) in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let il = Liveness_parser.main Liveness_lexer.token lexbuf in (* run the parser, producing AST *)
let (il2,ol2) = liveness il in 
(*print_instr_list il2; *)
exit 0
