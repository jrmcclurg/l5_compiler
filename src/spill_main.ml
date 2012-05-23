(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/9/2012
 *
 * Spill Test
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * spill_main.ml
 * This is the entry point for the Spill Test program.
 *)

open L2_ast;;
open L2_code;;
open Utils;;

(* program banner text *)
let banner_text = "Spill Test v. 1.0\n------------------";;

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
let (il,v,off,prefix) = Spill_parser.main Spill_lexer.token lexbuf in (* run the parser, producing AST *)
let il2 = spill il v off (get_symbol prefix) in 
print_instr_list il2;
exit 0
