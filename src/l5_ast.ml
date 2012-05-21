(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/21/2012
 *
 * L5-to-L4 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l5_ast.ml
 * This has the abstract data types for representing the
 * Abstract Syntax Tree (AST) for the parsed L5 program.
 *)

open Utils;;

(* unique prefix for auto-generated variables (NOTE: this begins with a "_" to avoid conflicting with keywords *)
let l5_prefix = "_l5";;

(* data type for L4 programs *)
type program = Program of pos * exp
 and exp = LambdaExp of pos * var list * exp
         | VarExp of pos * var
         | LetExp of pos * var * exp * exp
         | LetRecExp of pos * var * exp * exp
         | IfExp of pos * exp * exp * exp
         | NewTupleExp of pos * exp list
         | BeginExp of pos * exp * exp
         | AppExp of pos * exp * exp list
         | PrimExp of pos * prim
         | IntExp of pos * int64
 and prim = PlusPrim of pos
          | MinusPrim of pos
          | TimesPrim of pos
          | LtPrim of pos
          | LeqPrim of pos
          | EqPrim of pos
          | NumberPredPrim of pos
          | ArrayPredPrim of pos
          | PrintPrim of pos
          | NewArrayPrim of pos
          | ArefPrim of pos
          | AsetPrim of pos
          | AlenPrim of pos
 and var = Var of pos * int
;;

(* the output_... functions pretty-print L4 constructs to a specified channel *)

let rec output_program out (p : program) = match p with
  | Program(_,e) ->
     output_exp out e;
     output_string out "\n"
and output_exp out (e : exp) = match e with
   | LambdaExp(_,vl,e) ->
      output_string out "(lambda (";
      let _ = List.fold_left (fun flag v ->
         if flag then output_string out " ";
         output_var out v;
         true
      ) false vl in ();
      output_string out ")\n";
      output_exp out e;
      output_string out ")"
   | VarExp(_, r) -> output_var out r
   | LetExp(_, v, e1, e2) ->
      output_string out "(let ([";
      output_var out v;
      output_string out " ";
      output_exp out e1;
      output_string out "])\n  ";
      output_exp out e2;
      output_string out ")"
   | LetRecExp(_, v, e1, e2) ->
      output_string out "(letrec ([";
      output_var out v;
      output_string out " ";
      output_exp out e1;
      output_string out "])\n  ";
      output_exp out e2;
      output_string out ")"
   | IfExp(_, e1, e2, e3) ->
      output_string out "(if ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out " ";
      output_exp out e3;
      output_string out ")"
   | NewTupleExp(_,el) ->
      output_string out "(new-tuple";
      let _ = List.fold_left (fun _ et ->
         output_string out " ";
         output_exp out et;
         true
      ) false el in
      output_string out ")"
   | BeginExp(_,e1,e2) ->
      output_string out "(begin ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | AppExp(_,e,el) ->
      output_string out "(";
      output_exp out e;
      List.iter (fun et ->
         output_string out " ";
         output_exp out et
      ) el;
      output_string out ")"
   | PrimExp(_, p) ->
      output_prim out p
   | IntExp(_, i) -> output_string out (Int64.to_string i)
and output_prim out (pr : prim) = match pr with
   | PlusPrim(_) ->
      output_string out "+";
   | MinusPrim(_) ->
      output_string out "-";
   | TimesPrim(_) ->
      output_string out "*";
   | LtPrim(_) ->
      output_string out "<";
   | LeqPrim(_) ->
      output_string out "<=";
   | EqPrim(_) ->
      output_string out "=";
   | NumberPredPrim(_) ->
      output_string out "number?";
   | ArrayPredPrim(_) ->
      output_string out "a?";
   | PrintPrim(_) ->
      output_string out "print";
   | NewArrayPrim(_) ->
      output_string out "new-array";
   | ArefPrim(_) ->
      output_string out "aref";
   | AsetPrim(_) ->
      output_string out "aset";
   | AlenPrim(_) ->
      output_string out "alen";
and output_var out r = match r with
   | Var(_,s) -> output_string out (get_symbol s)
;;

(* the print_... functions pretty-print L4 constructs to stdout *)

let rec print_program p = output_program stdout p
and print_exp e = output_exp stdout e
and print_prim p = output_prim stdout p
and print_var r = output_var stdout r
;;
