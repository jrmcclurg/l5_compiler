(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/23/2012
 *
 * Graph Test
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * graph_main.ml
 * This is the entry point for the Graph Test program.
 *)

open L2_ast;;
open L2_code;;
open Utils;;

(* program banner text *)
let banner_text = "Graph Test v. 1.0\n------------------";;

(* parse the command-line arguments *)
let filename = ref "";;
Arg.parse [
] (fun x -> filename := x) banner_text;;

let print_vars_list vls sp =
   List.iter (fun vl ->
      print_string "(";
      List.iter (fun v -> 
         print_var v;
         print_string " "
      ) vl;
      print_string (")"^sp);
   ) vls
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
print_string "((in ";
print_vars_list il2 " ";
print_string ")\n(out ";
print_vars_list ol2 " ";
print_string "))\n"; 

let (ag,colors,ok) = graph_test il in
print_string "\n\n( ";
print_vars_list ag "\n";
print_string ")\n";
print_string "\n";
if ok then (
print_string "(";
List.iter (fun (v,c) -> 
   print_string "(";
   print_var v;
   print_string " ";
   print_var c;
   print_string ")\n"
) colors;
print_string ")\n" 
) else (
  print_string "#f\n"
);
exit 0
