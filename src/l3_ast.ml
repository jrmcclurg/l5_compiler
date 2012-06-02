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
let l3_prefix = "_l3";;

(* data type for L3 programs *)
type program = Program of pos * exp * func list
 and func = Function of pos * int * var list * exp
 and exp = LetExp of pos * var * dexp * exp
         | IfExp of pos * sval * exp * exp
         | DExpExp of pos * dexp
 and dexp = PlusDExp of pos * sval * sval
          | MinusDExp of pos * sval * sval
          | TimesDExp of pos * sval * sval
          | LtDExp of pos * sval * sval
          | LeqDExp of pos * sval * sval
          | EqDExp of pos * sval * sval
          | NumberPredDExp of pos * sval
          | ArrayPredDExp of pos * sval
          | AppDExp of pos * sval * sval list
          | NewArrayDExp of pos * sval * sval
          | NewTupleDExp of pos * dexp list
          | ArefDExp of pos * sval * sval
          | AsetDExp of pos * sval * sval * sval * bool
          | AlenDExp of pos * sval
          | PrintDExp of pos * sval
          | MakeClosureDExp of pos * int * sval
          | ClosureProcDExp of pos * sval
          | ClosureVarsDExp of pos * sval
          | SValDExp of pos * sval
 and sval = VarSVal of pos * var
          | IntSVal of pos * int32
          | LabelSVal of pos * int
 and var = Var of pos * int
;;

(*let normalize_exp (e : exp) =
  match e with
  | DExpExp(p,NewTupleDExp(p2,dl)) ->
     let (lets,dl2) = List.fold_right (fun d (lets,dl2) ->
        match d with
	| SValDExp(p,s) -> (lets,d::dl2)
	| _ -> 
	   let uv = Var(p,get_unique_symbol l3_prefix) in
	   ((uv,d)::lets, SValDExp(p,VarSVal(p,uv))::dl2)
     ) dl ([],[]) in
     List.fold_left (fun res (x,e) -> 
        LetExp(p,x,e,res)
     ) (DExpExp(p,NewTupleDExp(p2,dl2))) lets
  | _ -> e
;;*)

(* the output_... functions pretty-print L3 constructs to a specified channel *)

let rec output_program out p = match p with
  | Program(_,e,fl) ->
     output_string out "(\n  ";
     output_exp out e;
     output_string out "\n";
     let _ = List.fold_left (fun flag f ->
        if flag then output_string out "\n";
        output_func out f;
        output_string out "\n";
        true
     ) false fl in ();
     output_string out "\n)\n"
and output_func out f = match f with
  | Function(_,n,vl,e) ->
     output_string out ("  (:"^(get_symbol n)^" (");
     let _ = List.fold_left (fun flag i ->
        if flag then output_string out " ";
        output_var out i;
        true
     ) false vl in ();
     output_string out ") ";
     output_exp out e;
     output_string out "  )"
and output_exp out e =
   (*let e = normalize_exp e2 inA*)
   match e with
   | LetExp(_, v, de, e) ->
      output_string out "(let ([";
      output_var out v;
      output_string out " ";
      output_dexp out de;
      output_string out "])\n  ";
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
   | PlusDExp(_,sv1,sv2) ->
      output_string out "(+ ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | MinusDExp(_,sv1,sv2) ->
      output_string out "(- ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | TimesDExp(_,sv1,sv2) ->
      output_string out "(* ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | LtDExp(_,sv1,sv2) ->
      output_string out "(< ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | LeqDExp(_,sv1,sv2) ->
      output_string out "(<= ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | EqDExp(_,sv1,sv2) ->
      output_string out "(= ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | NumberPredDExp(_,sv) ->
      output_string out "(number? ";
      output_sval out sv;
      output_string out ")"
   | ArrayPredDExp(_,sv) ->
      output_string out "(a? ";
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
	 output_dexp out svt;
	 true
      ) false svl in
      output_string out ")"
   | ArefDExp(_,sv1,sv2) ->
      output_string out "(aref ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out ")"
   | AsetDExp(_,sv1,sv2,sv3,_) ->
      output_string out "(aset ";
      output_sval out sv1;
      output_string out " ";
      output_sval out sv2;
      output_string out " ";
      output_sval out sv3;
      output_string out ")"
   | AlenDExp(_,sv) ->
      output_string out "(alen ";
      output_sval out sv;
      output_string out ")"
   | PrintDExp(_,sv) ->
      output_string out "(print ";
      output_sval out sv;
      output_string out ")"
   | MakeClosureDExp(_,s,sv) ->
      output_string out "(make-closure ";
      output_string out (":"^(get_symbol s));
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
   | Var(_,s) -> output_string out (get_symbol s)
and output_sval out s = match s with
   | VarSVal(_, r) -> output_var out r
   | IntSVal(_, i) -> output_string out (Int32.to_string i)
   | LabelSVal(_,s) -> output_string out (":"^(get_symbol s))
;;

(* the print_... functions pretty-print L3 constructs to stdout *)

let rec print_program p = output_program stdout p
and print_func f = output_func stdout f
and print_exp e = output_exp stdout e
and print_dexp de = output_dexp stdout de
and print_var r = output_var stdout r
and print_sval s = output_sval stdout s
;;

let dexp_list_is_flat dl =
   List.fold_left (fun res sv ->
   match (res,sv) with
      | (true,_) -> res
      | (_,SValDExp(p,_)) -> res
      | (_,_) -> true
   ) false dl
;;
