(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/21/2012
 *
 * L5-to-L4 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l5_main.ml
 *)

open L5_ast;;
open L5_code;;
open Utils;;

(* flags and defaults for command-line args *)
let out_file_name      = ref (None : string option);;
let binary_file_name   = ref "a.out";;
let do_parse_only      = ref false;;
let do_compile_only    = ref false;;

(* program banner text *)
let banner_text = "L5 Compiler v. 1.0\n------------------";;

(* parse the command-line arguments *)
let filename = ref "";;
Arg.parse [
   ("-parse",    Arg.Unit(fun x -> do_parse_only := true; do_compile_only := false),
                    "Output the parsed L5 code and exit (default location: stdout)");
   ("-compile",  Arg.Unit(fun x -> do_compile_only := true; do_parse_only := false),
                    "Do the full L5->L4->L3->L2->L1 compilation (default location: a.out)");
   ("-o",        Arg.String(fun x -> out_file_name := Some(x); binary_file_name := x),
                    "Location of the result")
] (fun x -> filename := x) banner_text;;

(* use the command-line filename if one exists, otherwise use stdin *)
let in_stream = if (!filename="") then stdin else (
   try (open_in !filename)
   with _ -> die_system_error ("can't read from file: "^(!filename))
) in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = L5_parser.main L5_lexer.token lexbuf in (* run the parser, producing AST *)
(* if we only need to print the parsed L1 code, do so *)
if !do_compile_only then (
   let p4 = compile_program result in      (* compile from L5 to L4 *)
   let p3 = L4_code.compile_program p4 in  (* compile from L4 to L3 *)
   let p2 = L3_code.compile_program p3 in  (* compile from L3 to L2 *)
   let p1 = L2_code.compile_program p2 in  (* compile from L2 to L1 *)
   L1_code.generate_binary p1 !binary_file_name
) else (
   let out_stream = (match !out_file_name with
   | None -> stdout
   | Some(name) ->
      try (open_out name)
      with _ -> die_system_error ("can't read from file: "^name)
   ) in
   if !do_parse_only then (
      output_program out_stream result;
      output_string out_stream "\n"
   ) else (
      let p = compile_program result in
      L4_ast.output_program out_stream p
   )
);
exit 0