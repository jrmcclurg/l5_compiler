(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/3/2012
 *
 * L2-to-L1 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l2_main.ml
 * This will be the starting point for the L2 compiler
 *)

open L2_ast;;
open L2_code;;
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
   ("-v",        Arg.Unit(fun x -> verbose_mode := true),
                    "Turn on verbose output");
   ("-parse",    Arg.Unit(fun x -> do_print_only := true),
                    "Print the parsed L1 code and exit");
   ("-o",        Arg.String(fun x -> output_file_name := x),
                    "Location of the compiled result (default: a.out)")
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
(* if we only need to print the parsed L1 code, do so *)
if !do_print_only then (
   print_instr_list il;
   print_newline ();
   let il2 = spill il v off prefix in 
   print_instr_list il2
);
exit 0
