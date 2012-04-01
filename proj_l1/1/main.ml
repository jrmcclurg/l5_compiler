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

open Utils;;

(* flags and defaults for command-line args *)
let assembly_file_name = ref "prog.S";;
let runtime_file_name  = ref "runtime.c";;
let output_file_name   = ref "a.out";;
let use_32bit_arch     = ref true;;
let do_print_only      = ref false;;
let verbose_mode       = ref false;;

(* program banner text *)
let banner_text = "L1 Compiler v. 1.0\n------------------";;

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

(* use the command-line filename if one exists, otherwise use stdin *)
let in_stream = if (!filename="") then stdin else (
   try (open_in !filename)
   with _ -> die_system_error ("can't read from file: "^
      (Sys.getcwd ())^"/"^(!filename))
) in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = Parser.main Lexer.token lexbuf in (* run the parser, producing AST *)
(* if we only need to print the parsed L1 code, do so *)
if !do_print_only then (
   Ast.print_program result;
   print_newline()
) else ( (* if we need to actually compile to assembly, do so *)
   (* generate the C runtime *)
   let out1 = (try (open_out !runtime_file_name)
      with _ -> die_system_error ("can't write to file: "^
         (Sys.getcwd ())^"/"^(!runtime_file_name))
   ) in
   Code.generate_runtime out1;
   close_out out1;
   (* generate the assembly code *)
   let out2 = (try (open_out !assembly_file_name)
      with _ -> die_system_error ("can't write to file: "^
      (Sys.getcwd ())^"/"^(!assembly_file_name))
   ) in
   Code.compile_program out2 result;
   close_out out2;
   (* compile and link everything *)
   Code.compile_and_link !output_file_name !use_32bit_arch;
   (* if verbose mode is enabled, print a summary *)
   if !verbose_mode then (
      print_string (banner_text^"\n");
      print_string ("Generated C runtime:    "^(!runtime_file_name)^"\n");
      print_string ("Generated x86 assembly: "^(!assembly_file_name)^"\n");
      print_string ("Generated "^(if !use_32bit_arch then "32" else "64")^
                                 "bit binary: "^(!output_file_name)^"\n")
   )
);
exit 0
