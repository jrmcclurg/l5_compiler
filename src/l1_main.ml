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

(* flags and defaults for command-line args *)
let output_file_name   = ref "a.out";;
let custom_out_file    = ref false;;
let use_32bit_arch     = ref true;;
let do_parse_only      = ref false;;
let do_compile_only    = ref true;;
let verbose_mode       = ref false;;

(* program banner text *)
let banner_text = "L1 Compiler v. 1.0\n------------------";;

(* parse the command-line arguments *)
let filename = ref "";;
Arg.parse [
   ("-v",        Arg.Unit(fun x -> verbose_mode := true),
                    "Turn on verbose output");
   ("-parse",    Arg.Unit(fun x -> do_parse_only := true; do_compile_only := false),
                    "Print the parsed L1 code and exit");
   ("-compile",  Arg.Unit(fun x -> do_compile_only := true; do_parse_only := false),
                    "Print the parsed L1 code and exit");
   ("-debug",    Arg.String(fun x -> add_debug x),
                    "Add a debug option");
   ("-heap",     Arg.Int(fun x -> heap_size := x),
                    "Set the heap size (default 1048576)");
   ("-o",        Arg.String(fun x -> output_file_name := x; custom_out_file := true),
                    "Location of the compiled result (default: a.out)")
] (fun x -> filename := x) banner_text;;

(* use the command-line filename if one exists, otherwise use stdin *)
let in_stream = if (!filename="") then stdin else (
   try (open_in !filename)
   with _ -> die_system_error ("can't read from file: "^
      (!filename))
) in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = L1_parser.main L1_lexer.token lexbuf in (* run the parser, producing AST *)
(* if we only need to print the parsed L1 code, do so *)
if !do_parse_only then (
   let out_stream = if (not !custom_out_file) then stdout else (
      try (open_out !output_file_name)
      with _ -> die_system_error ("can't read from file: "^
         (!output_file_name))
      ) in
   output_program out_stream result;
   output_string out_stream "\n"
) else if !do_compile_only then ( (* if we need to actually compile to assembly, do so *)
   generate_binary result !output_file_name
);
exit 0
