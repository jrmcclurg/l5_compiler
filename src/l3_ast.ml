(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/6/2012
 *
 * L3-to-L2 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l3_ast.ml
 * This has the abstract data types for representing the
 * Abstract Syntax Tree (AST) for the parsed L3 program.
 *)

open Utils;;

(* unique prefix for auto-generated variables *)
let l3_prefix = get_prefix "l3";; (* TODO XXX - do this for L2 as well!! *)

(* data type for L3 programs *)
type program = Program of pos * exp * func list
 and func = Function of pos * string * var list * exp
 and exp = LetExp of pos * var * dexp * exp
         | IfExp of pos * sval * exp * exp
         | DExpExp of pos * dexp
 and dexp = BiopDExp of pos * biop * sval * sval
          | PredDExp of pos * pred * sval
          | AppDExp of pos * sval * sval list
          | NewArrayDExp of pos * sval * sval
          | NewTupleDExp of pos * sval list
          | ArefDExp of pos * sval * sval
          | AsetDExp of pos * sval * sval
          | AlenDExp of pos * sval * sval
          | PrintDExp of pos * sval
          | MakeClosureDExp of pos * string * sval
          | ClosureProcDExp of pos * sval
          | ClosureVarsDExp of pos * sval
          | SValDExp of pos * sval
 and sval = VarSVal of pos * var
          | IntSVal of pos * int64
          | LabelSVal of pos * string
 and var = Var of pos * string (* TODO XXX - eventually we need a symbol table *)
 and biop = PlusBiop of pos
          | MinusBiop of pos
          | TimesBiop of pos
          | LtBiop of pos
          | LeqBiop of pos
          | EqBiop of pos
 and pred = NumberPred of pos * int64
          | VarPred of pos * var
;;

(* the output_... functions pretty-print L3 constructs to a specified channel *)

let rec output_program out p = match p with
  | Program(_,e,fl) ->
     output_string out "(\n  ";
     output_exp out e;
     output_string out "\n";
     let _ = List.fold_left (fun flag f ->
        if flag then output_string out "\n";
        output_func out f;
        true
     ) false fl in ();
     output_string out "\n)"
and output_func out f = match f with
  | Function(_,n,vl,e) ->
     output_string out ("  (:"^n^" (");
     let _ = List.fold_left (fun flag i ->
        if flag then output_string out " ";
        output_var out i;
        true
     ) false vl in ();
     output_string out ") ";
     output_exp out e;
     output_string out "  )"
and output_exp out e = match e with
   | LetExp(_, v, de, e) ->
      output_string out "(let ([";
      output_var out v;
      output_string out " ";
      output_dexp out de;
      output_string out "]) ";
      output_exp out e;
      output_string out ")"
   | IfExp(_, sv, e1, e2) ->
      output_string out "(if ";
      output_sval out sv;
      output_string out " ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | DExpExp(_, de) ->
      output_dexp out de
and output_dexp out de = match de with
   | BiopDExp(_,b,sv1,sv2) ->
      output_string out "(";
      output_biop out b;
      output_string out " ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | PredDExp(_,p,sv) ->
      output_string out "(";
      output_pred out p;
      output_string out " ";
      output_sval out sv;
      output_string out ")"
   | AppDExp(_,sv,svl) ->
      output_string out "(";
      output_sval out sv;
      List.iter (fun svt ->
         output_string out " ";
         output_sval out svt
      ) svl;
      output_string out ")"
   | NewArrayDExp(_,sv1,sv2) ->
      output_string out "(new-array ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | NewTupleDExp(_,svl) ->
      output_string out "(new-tuple";
      let _ = List.fold_left (fun _ svt ->
         output_string out " ";
         output_sval out svt;
         true
      ) false svl in
      output_string out ")"
   | ArefDExp(_,sv1,sv2) ->
      output_string out "(aref ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | AsetDExp(_,sv1,sv2) ->
      output_string out "(aset ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | AlenDExp(_,sv1,sv2) ->
      output_string out "(alen ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | PrintDExp(_,sv) ->
      output_string out "(print ";
      output_sval out sv;
      output_string out ")"
   | MakeClosureDExp(_,s,sv) ->
      output_string out "(make-closure ";
      output_string out (":"^s);
      output_string out " ";
      output_sval out sv;
      output_string out ")"
   | ClosureProcDExp(_,sv) ->
      output_string out "(closure-proc ";
      output_sval out sv;
      output_string out ")"
   | ClosureVarsDExp(_,sv) ->
      output_string out "(closure-vars ";
      output_sval out sv;
      output_string out ")"
   | SValDExp(_, sv) ->
      output_sval out sv
and output_var out r = match r with
   | Var(_,s) -> output_string out s
and output_sval out s = match s with
   | VarSVal(_, r) -> output_var out r
   | IntSVal(_, i) -> output_string out (Int64.to_string i)
   | LabelSVal(_,s) -> output_string out (":"^s)
and output_biop out b = match b with
   | PlusBiop(_) -> output_string out "+"
   | MinusBiop(_) -> output_string out "-"
   | TimesBiop(_) -> output_string out "*"
   | LtBiop(_) -> output_string out "<"
   | LeqBiop(_) -> output_string out "<="
   | EqBiop(_) -> output_string out "="
and output_pred out p = match p with
   | NumberPred(_, i) -> output_string out ((Int64.to_string i)^"?")
   | VarPred(_,v) -> output_var out v; output_string out "?"
;;

(* the print_... functions pretty-print L3 constructs to stdout *)

let rec print_program p = output_program stdout p
and print_func f = output_func stdout f
and print_exp e = output_exp stdout e
and print_dexp de = output_dexp stdout de
and print_var r = output_var stdout r
and print_sval s = output_sval stdout s
and print_biop b = output_biop stdout b
and print_pred p = output_pred stdout p
;;
