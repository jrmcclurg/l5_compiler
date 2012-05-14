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

(* flags and defaults for command-line args *)
let out_file_name      = ref (None : string option);;
let binary_file_name   = ref "a.out";;
let do_parse_only      = ref false;;
let do_compile_only    = ref false;;

(* program banner text *)
let banner_text = "L4 Compiler v. 1.0\n------------------";;

(* parse the command-line arguments *)
let filename = ref "";;
Arg.parse [
   ("-parse",    Arg.Unit(fun x -> do_parse_only := true; do_compile_only := false),
                    "Output the parsed L4 code and exit (default location: stdout)");
   ("-compile",  Arg.Unit(fun x -> do_compile_only := true; do_parse_only := false),
                    "Do the full L4->L3->L2->L1 compilation (default location: a.out)");
   ("-o",        Arg.String(fun x -> out_file_name := Some(x); binary_file_name := x),
                    "Location of the result")
] (fun x -> filename := x) banner_text;;

(* use the command-line filename if one exists, otherwise use stdin *)
let in_stream = if (!filename="") then stdin else (
   try (open_in !filename)
   with _ -> die_system_error ("can't read from file: "^(!filename))
) in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let result = L4_parser.main L4_lexer.token lexbuf in (* run the parser, producing AST *)
(* if we only need to print the parsed L1 code, do so *)
if !do_compile_only then (
   let p3 = compile_program result in      (* compile from L4 to L3 *)
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
      match result with
      | Program(_,e,_) ->
      let (vo,eo,test,i) = get_first_exp e 0 in
      print_string "Here is the expression\n";
      print_exp e;
      print_string "\nNow here is the env:\n";
      print_exp test;
      print_string "\nHere is the pulled out expr:\n";
      (match eo with
      | None -> ()
      | Some(ex) -> print_exp ex);
      print_string "\nNow here is the i:\n";
      print_int i;
      print_string "\n";
      let (xo,eo,env,i) = get_first_exp e 0 in
      print_string "ENV:\n";
      print_exp env;
      (match (xo,eo) with
      | (Some(x),Some(e)) -> print_exp (flatten_exp env x e) ; ()
      | _ -> 
         print_string "Returning to the user: \""; );

      print_string "ENV:\n";
      print_exp env;
      (match (xo,eo) with
      | (Some(x),Some(e)) -> print_exp (flatten_exp env x e) ; ()
      | _ -> 
         print_string "Returning to the user: \""; );
      (*let p = compile_program result in () *)
      (*L3_ast.output_program out_stream p*)
   )
);
exit 0
