(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/14/2012
 *
 * L4-to-L3 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l4_code.ml
 * Contains the l4-to-l3 compilation
 * functionality.
 *)

open L4_ast;;
open Utils;;

(*********************************************************
 **  L4-to-L3 CODE GENERATION                           **
 *********************************************************)

(*
 * In the expression e, replace all instances of target with repl
 *)
let rec replace_in_exp (ex : L4_ast.exp) (target : L4_ast.var) (repl : L4_ast.exp) : L4_ast.exp =
   match ex with
   | LetExp(p,v,e1,e2) ->
      (* if this let binds a variable with same name as target, don't replace in the body *)
      let equal = (match (v,target) with
                 | (Var(_,s1),Var(_,s2)) -> (s1 = s2)) in
      LetExp(p, v, replace_in_exp e1 target repl,
                   if equal then e2 else (replace_in_exp e2 target repl))
   | IfExp(p,e1,e2,e3) -> IfExp(p, replace_in_exp e1 target repl,
                                   replace_in_exp e2 target repl,
                                   replace_in_exp e3 target repl)
   | AppExp(p,e,el) -> AppExp(p, replace_in_exp e target repl,
                                 List.map (fun ex -> replace_in_exp ex target repl) el)
   | NewArrayExp(p,e1,e2) -> NewArrayExp(p, replace_in_exp e1 target repl,
                                            replace_in_exp e2 target repl)
   | NewTupleExp(p,el) -> NewTupleExp(p, List.map (fun ex -> replace_in_exp ex target repl) el)
   | ArefExp(p,e1,e2) -> ArefExp(p, replace_in_exp e1 target repl,
                                    replace_in_exp e2 target repl)
   | AsetExp(p,e1,e2,e3) -> AsetExp(p, replace_in_exp e1 target repl,
                                       replace_in_exp e2 target repl,
                                       replace_in_exp e3 target repl)
   | AlenExp(p,e1) -> AlenExp(p, replace_in_exp e1 target repl);
   | BeginExp(p,e1,e2) -> BeginExp(p, replace_in_exp e1 target repl,
                                      replace_in_exp e2 target repl)
   | PrintExp(p,e) -> PrintExp(p, replace_in_exp e target repl)
   | MakeClosureExp(p,s,e) -> MakeClosureExp(p, s, replace_in_exp e target repl)
   | ClosureProcExp(p,e) -> ClosureProcExp(p, replace_in_exp e target repl)
   | ClosureVarsExp(p,e) -> ClosureVarsExp(p, replace_in_exp e target repl)
   | PlusExp(p,e1,e2) -> PlusExp(p, replace_in_exp e1 target repl,
                                    replace_in_exp e2 target repl)
   | MinusExp(p,e1,e2) -> MinusExp(p, replace_in_exp e1 target repl,
                                      replace_in_exp e2 target repl)
   | TimesExp(p,e1,e2) -> TimesExp(p, replace_in_exp e1 target repl,
                                      replace_in_exp e2 target repl)
   | LtExp(p,e1,e2) -> LtExp(p, replace_in_exp e1 target repl,
                                replace_in_exp e2 target repl)
   | LeqExp(p,e1,e2) -> LeqExp(p, replace_in_exp e1 target repl,
                                  replace_in_exp e2 target repl)
   | EqExp(p,e1,e2) -> EqExp(p, replace_in_exp e1 target repl,
                                replace_in_exp e2 target repl)
   | NumberPredExp(p,e) -> NumberPredExp(p, replace_in_exp e target repl)
   | ArrayPredExp(p,e) -> ArrayPredExp(p, replace_in_exp e target repl)
   | VarExp(p,Var(p2,s)) -> 
      (* if this equals the target variable, do the replacement *)
      let ts = (match target with
                | Var(_,s1) -> s1) in
      if (ts = s) then ex else (VarExp(p,target))
   | IntExp(_,_) -> ex
   | LabelExp(_,_) -> ex
;;

(* 
 * Where e is an expression with the extraction site labeled with x,
 * and bad is the thing to extract (b,x are returned by check_extraction)
*)
let flatten_exp (e : L4_ast.exp) (x : L4_ast.var) (extracted: L4_ast.exp) : (L4_ast.exp) =
   match extracted with
   | LetExp(p,v,e1,e2) -> L4_ast.LetExp(p,x,e1,replace_in_exp (replace_in_exp e x e2) v (VarExp(p,x)))
   | IfExp(p,e1,e2,e3) -> L4_ast.IfExp(p,e1,replace_in_exp e x e2,replace_in_exp e x e3)
   | AppExp(p,e,el) ->    L4_ast.LetExp(p,x,extracted,e) 
   | NewArrayExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,e) 
   | NewTupleExp(p,el) ->    L4_ast.LetExp(p,x,extracted,e) 
   | ArefExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,e) 
   | AsetExp(p,e1,e2,e3) ->    L4_ast.LetExp(p,x,extracted,e) 
   | AlenExp(p,e1) ->    L4_ast.LetExp(p,x,extracted,e) 
   | BeginExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,e) 
   | PrintExp(p,e) ->    L4_ast.LetExp(p,x,extracted,e) 
   | MakeClosureExp(p,s,e) ->    L4_ast.LetExp(p,x,extracted,e) 
   | ClosureProcExp(p,e) ->    L4_ast.LetExp(p,x,extracted,e) 
   | ClosureVarsExp(p,e) ->    L4_ast.LetExp(p,x,extracted,e) 
   | PlusExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,e) 
   | MinusExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,e) 
   | TimesExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,e) 
   | LtExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,e) 
   | LeqExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,e) 
   | EqExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,e) 
   | NumberPredExp(p,e) ->    L4_ast.LetExp(p,x,extracted,e) 
   | ArrayPredExp(p,e) ->      L4_ast.LetExp(p,x,extracted,e)
   | VarExp(p,s) ->            e
   | IntExp(p,i) ->            e
   | LabelExp(p,s) ->          e
;;

(* 
 * Checks if an expression is flat, and if not, returns a
 * fresh variable to be used as a replacement for the expression)
 *)
let rec is_flattenable (e : L4_ast.exp) (stop_d : bool) : (L4_ast.var option) =
   match e with
   | LetExp(p,v,e1,e2) -> Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | IfExp(p,e1,e2,e3) -> Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | AppExp(p,e,el) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None (e::el)
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | NewArrayExp(p,e1,e2) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | NewTupleExp(p,el) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None el
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | ArefExp(p,e1,e2) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | AsetExp(p,e1,e2,e3) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2;e3]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | AlenExp(p,e1) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | BeginExp(p,e1,e2) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | PrintExp(p,e) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | MakeClosureExp(p,s,e) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | ClosureProcExp(p,e) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | ClosureVarsExp(p,e) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | PlusExp(p,e1,e2) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | MinusExp(p,e1,e2) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | TimesExp(p,e1,e2) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | LtExp(p,e1,e2) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | LeqExp(p,e1,e2) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | EqExp(p,e1,e2) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e1;e2]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | NumberPredExp(p,e) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | ArrayPredExp(p,e) ->
      if stop_d then (
         List.fold_left (fun r e -> 
            match r with
            | Some(_) -> r
            | _ -> is_flattenable e stop_d
         ) None [e]
      ) else Some(L4_ast.Var(p,get_unique_ident l4_prefix))
   | VarExp(p,s) -> None
   | IntExp(p,i) -> None
   | LabelExp(p,s) -> None
;;

(* 
 * Given a list like (a b c (+ (1 2) (3 4)) e f), returns the tuple
 * X, (+ (1 2) (3 4)), (a b c X e f)  where X is a fresh variable
 * if stop_d is true, dexp will not be reduced to variables
 *)
let get_first_flattenable (el : L4_ast.exp list) (stop_d : bool) : (L4_ast.var option * L4_ast.exp option * L4_ast.exp list) =
   List.fold_left (fun (vt,et,elt) e -> 
      print_string "Checking flattenable: ";
      print_exp e;
      match vt with
      | None ->
         let vo = is_flattenable e stop_d in
         (match vo with
         | None -> (vt,et,elt@[e])
         | Some((Var(p,s)) as vr) -> print_string "YES!"; (Some(vr),Some(e),elt@[VarExp(p,vr)]))
      | _ -> (vt,et,elt@[e])
   ) (None,None,[]) el
;;

(* compile an L4 program into an L3 program *)

let rec compile_program (pr : L4_ast.program) : L3_ast.program =
   match pr with
   | Program(p,e,fl) -> L3_ast.Program(p,compile_exp e,List.map (fun f -> compile_func f) fl)

and compile_func (f : L4_ast.func) : L3_ast.func =
   match f with
   | Function(p,name,vl,e) -> L3_ast.Function(p, name, List.map (fun v -> compile_var v) vl, compile_exp e)

and compile_exp (the_exp : L4_ast.exp) : L3_ast.exp = 
   print_string "COMPILING: ";
   print_exp the_exp;
   print_string "\n";
   match the_exp with
   (* (let ([v (let ([v2 e1]) e2)]) e3)  -->  (let ([v2 e1]) (let ([v e2]) e3)) *)
   (*| LetExp(p,v,LetExp(p2,v2,e1,e2),e3) -> compile_exp (LetExp(p,v2,e1,LetExp(v,e2,e3)))*)
   (* (let ([v (if v2 e1 e2)]) e3)  -->  (if v2 (let ([v e1]) e3) (let ([v e2]) e3)) *)
   (*| LetExp(p,v,IfExp(p2,e1,e2,e3),e4) -> compile_exp (IfExp(p,v2,LetExp(p,v,e1,e3),LetExp(p,v,e2,e3)))*)
   (*| LetExp(p,v,e1,e2) -> L3_ast.LetExp(p, compile_var v, compile_exp_to_dexp e1, compile_exp e2)*)

   | LetExp(p,v,e1,e2) -> 
      let el = [e1] in
      let (xo,eo,el2) = get_first_flattenable el true in
      let p2 = LetExp(p,v,List.nth el2 0,e2) in
      (match (xo,eo) with
      | (Some(x),Some(e)) -> compile_exp (flatten_exp p2 x e)
      | _ ->
         print_string "Returning to the user: \"";
         let result = L3_ast.LetExp(p,compile_var v, compile_exp_to_dexp e1,compile_exp e2) in
         L3_ast.print_exp result;
         print_string "\"\n";
         result)
   (*| IfExp(p,e1,e2,e3) -> 
   | AppExp(p,e,el) -> 
   | NewArrayExp(p,e1,e2) -> 
   | NewTupleExp(p,el) -> 
   | ArefExp(p,e1,e2) ->
   | AsetExp(p,e1,e2,e3) ->
   | AlenExp(p,e1) ->
   | BeginExp(p,e1,e2) -> 
   | PrintExp(p,e) -> 
   | MakeClosureExp(p,s,e) ->
   | ClosureProcExp(p,e) -> *)
   | PlusExp(p,e1,e2) ->
      let el = [e1;e2] in
      let (xo,eo,el2) = get_first_flattenable el false in
      let p2 = PlusExp(p,List.nth el2 0,List.nth el2 1) in
      (match (xo,eo) with
      | (Some(x),Some(e)) -> compile_exp (flatten_exp p2 x e)
      | _ -> L3_ast.DExpExp(p,L3_ast.PlusDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2)))
   (*| MinusExp(p,e1,e2) -> 
   | TimesExp(p,e1,e2) -> 
   | LtExp(p,e1,e2) -> 
   | LeqExp(p,e1,e2) -> 
   | EqExp(p,e1,e2) -> 
   | NumberPredExp(p,e) -> 
   | ArrayPredExp(p,e) -> 
   | VarExp(p,v) -> 
   | IntExp(p,i) -> 
   | LabelExp(p,s) ->*)

and compile_exp_to_dexp (e : L4_ast.exp) : L3_ast.dexp =
   match e with
   | AppExp(p,e,el) -> L3_ast.AppDExp(p,compile_exp_to_sval e, List.map (fun ex -> compile_exp_to_sval ex) el)
   | NewArrayExp(p,e1,e2) -> L3_ast.NewArrayDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | NewTupleExp(p,el) -> L3_ast.NewTupleDExp(p,List.map (fun ex -> compile_exp_to_sval ex) el)
   | ArefExp(p,e1,e2) -> L3_ast.ArefDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | AsetExp(p,e1,e2,e3) -> L3_ast.AsetDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2,compile_exp_to_sval e3)
   | AlenExp(p,e) -> L3_ast.AlenDExp(p,compile_exp_to_sval e)
   | PrintExp(p,e) -> L3_ast.PrintDExp(p,compile_exp_to_sval e)
   | MakeClosureExp(p,s,e) -> L3_ast.MakeClosureDExp(p,s,compile_exp_to_sval e)
   | ClosureProcExp(p,e) -> L3_ast.ClosureProcDExp(p,compile_exp_to_sval e)
   | PlusExp(p,e1,e2) -> L3_ast.PlusDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | MinusExp(p,e1,e2) -> L3_ast.MinusDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | TimesExp(p,e1,e2) -> L3_ast.TimesDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | LtExp(p,e1,e2) -> L3_ast.LtDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | LeqExp(p,e1,e2) -> L3_ast.LeqDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | EqExp(p,e1,e2) -> L3_ast.EqDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | NumberPredExp(p,e) -> L3_ast.NumberPredDExp(p,compile_exp_to_sval e)
   | ArrayPredExp(p,e) -> L3_ast.ArrayPredDExp(p, compile_exp_to_sval e)
   | VarExp(p,v) -> L3_ast.SValDExp(p,L3_ast.VarSVal(p,compile_var v))
   | IntExp(p,i) -> L3_ast.SValDExp(p,L3_ast.IntSVal(p,i))
   | LabelExp(p,s) -> L3_ast.SValDExp(p,L3_ast.LabelSVal(p,s))
   | _ -> print_exp e; die_system_error "expected a dexp"

and compile_exp_to_sval (e : L4_ast.exp) : L3_ast.sval =
   match e with
   | VarExp(p,v) -> L3_ast.VarSVal(p,compile_var v)
   | IntExp(p,i) -> L3_ast.IntSVal(p,i)
   | LabelExp(p,s) -> L3_ast.LabelSVal(p,s)
   | _ -> print_exp e; die_system_error "expected an sval"

and compile_var (v : L4_ast.var) : L3_ast.var =
   match v with
   | Var(p,s) -> L3_ast.Var(p,s)
;;
