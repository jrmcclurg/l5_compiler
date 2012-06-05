(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/14/2012
 *
 * L4-to-L3 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l4_ast.ml
 * This has the abstract data types for representing the
 * Abstract Syntax Tree (AST) for the parsed L4 program.
 *)

open Utils;;

(* unique prefix for auto-generated variables (NOTE: this begins with a "_" to avoid conflicting with keywords *)
let l4_prefix = "_l4";;

(* data type for L4 programs *)
type program = Program of pos * exp * func list
 and func = Function of pos * int * var list * exp
 and exp = LetExp of pos * var * exp * exp
         | IfExp of pos * exp * exp * exp
         | AppExp of pos * exp * exp list
         | NewArrayExp of pos * exp * exp
         | NewTupleExp of pos * exp list
         | ArefExp of pos * exp * exp
         | AsetExp of pos * exp * exp * exp
         | AlenExp of pos * exp
         | BeginExp of pos * exp * exp
         | PrintExp of pos * exp
         | MakeClosureExp of pos * int * exp
         | ClosureProcExp of pos * exp
         | ClosureVarsExp of pos * exp
         | PlusExp of pos * exp * exp
         | MinusExp of pos * exp * exp
         | TimesExp of pos * exp * exp
         | LtExp of pos * exp * exp
         | LeqExp of pos * exp * exp
         | EqExp of pos * exp * exp
         | NumberPredExp of pos * exp
         | ArrayPredExp of pos * exp
         | VarExp of pos * var
         | IntExp of pos * int32
         | LabelExp of pos * int
 and var = Var of pos * int
;;

(* the output_... functions pretty-print L4 constructs to a specified channel *)

let rec output_program out (p : program) = match p with
  | Program(_,e,fl) ->
     output_string out "(\n  ";
     output_exp out e;
     output_string out "\n";
     let _ = List.fold_left (fun flag f ->
        if flag then output_string out "\n";
        output_string out "\n";
        output_func out f;
        true
     ) false fl in ();
     output_string out "\n)\n"
and output_func out (f : func) = match f with
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
and output_exp out (e : exp) = match e with
   | LetExp(_, v, e1, e2) ->
      output_string out "(let ([";
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
   | AppExp(_,e,el) ->
      output_string out "(";
      output_exp out e;
      List.iter (fun et ->
         output_string out " ";
         output_exp out et
      ) el;
      output_string out ")"
   | NewArrayExp(_,e1,e2) ->
      output_string out "(new-array ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | NewTupleExp(_,el) ->
      output_string out "(new-tuple";
      let _ = List.fold_left (fun _ et ->
         output_string out " ";
         output_exp out et;
         true
      ) false el in
      output_string out ")"
   | ArefExp(_,e1,e2) ->
      output_string out "(aref ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | AsetExp(_,e1,e2,e3) ->
      output_string out "(aset ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out " ";
      output_exp out e3;
      output_string out ")"
   | AlenExp(_,e) ->
      output_string out "(alen ";
      output_exp out e;
      output_string out ")"
   | BeginExp(_,e1,e2) ->
      output_string out "(begin ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | PrintExp(_,e) ->
      output_string out "(print ";
      output_exp out e;
      output_string out ")"
   | MakeClosureExp(_,s,e) ->
      output_string out "(make-closure ";
      output_string out (":"^(get_symbol s));
      output_string out " ";
      output_exp out e;
      output_string out ")"
   | ClosureProcExp(_,e) ->
      output_string out "(closure-proc ";
      output_exp out e;
      output_string out ")"
   | ClosureVarsExp(_,e) ->
      output_string out "(closure-vars ";
      output_exp out e;
      output_string out ")"
   | PlusExp(_,e1,e2) ->
      output_string out "(+ ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | MinusExp(_,e1,e2) ->
      output_string out "(- ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | TimesExp(_,e1,e2) ->
      output_string out "(* ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | LtExp(_,e1,e2) ->
      output_string out "(< ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | LeqExp(_,e1,e2) ->
      output_string out "(<= ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | EqExp(_,e1,e2) ->
      output_string out "(= ";
      output_exp out e1;
      output_string out " ";
      output_exp out e2;
      output_string out ")"
   | NumberPredExp(_,e) ->
      output_string out "(number? ";
      output_exp out e;
      output_string out ")"
   | ArrayPredExp(_,e) ->
      output_string out "(a? ";
      output_exp out e;
      output_string out ")"
   | VarExp(_, r) -> output_var out r
   | IntExp(_, i) -> output_string out (Int32.to_string i)
   | LabelExp(_,s) -> output_string out (":"^(get_symbol s))
and output_var out r = match r with
   | Var(_,s) -> output_string out (get_symbol s)
;;

(* the print_... functions pretty-print L4 constructs to stdout *)

let rec print_program p = output_program stdout p
and print_func f = output_func stdout f
and print_exp e = output_exp stdout e
and print_var r = output_var stdout r
;;
