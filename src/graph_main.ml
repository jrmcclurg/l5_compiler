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

(* print a list of (var list) *)
let print_vars_list vls sp =
   let vls2 = (List.sort (fun (a,_) (b,_) ->
      let id1 = get_var_id a in
      let id2 = get_var_id b in
      String.compare (get_symbol id1) (get_symbol id2)
   ) vls) in
   List.iter (fun (v,vl) ->
      print_string "(";
      print_var v;
      print_string " ";
      let vl2 = (List.sort (fun a b ->
         let id1 = get_var_id a in
         let id2 = get_var_id b in
         (* print_string (">>> comparing "^(get_symbol id1)^" with "^(get_symbol id2)^"<<<\n");
         flush stdout; *)
         String.compare (get_symbol id1) (get_symbol id2)
      ) (VarSet.elements vl)) in
      List.iter (fun v -> 
         print_var v;
         print_string " "
      ) vl2;
      print_string (")"^sp);
   ) vls2
;;

(* use the command-line filename if one exists, otherwise use stdin *)
let in_stream = if (!filename="") then stdin else (
   try (open_in !filename)
   with _ -> die_system_error ("can't read from file: "^
      (Sys.getcwd ())^"/"^(!filename))
) in
let lexbuf = Lexing.from_channel in_stream in  (* instantiate the lexer *)
let il = Liveness_parser.main Liveness_lexer.token lexbuf in (* run the parser, producing AST *)
(* get the adjacency list (ag),
 * register assignments (colors), and
 * any error message (ok) *)
let (ag,colors,ok,_) = graph_color il in
(* print the adjacency list *)
print_string "\n\n( ";
print_vars_list ag "\n";
print_string ")\n";
print_string "\n";
(* if the graph was colorable... *)
if ok then (
print_string "(";
(* print assignments of colors (i.e. registers) to variables *)
List.iter (fun (v,c) -> 
   print_string "(";
   print_var v;
   print_string " ";
   print_var c;
   print_string ")\n"
) (List.sort (fun (a,_) (b,_) -> 
   let id1 = get_var_id a in
   let id2 = get_var_id b in
   String.compare (get_symbol id1) (get_symbol id2)
) colors);
print_string ")\n" 
(* if the graph was not colorable, print error *)
) else (
  print_string "#f\n"
);
exit 0
