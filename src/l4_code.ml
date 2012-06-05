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
open Flags;;

(*********************************************************
 **  L4-to-L3 CODE GENERATION                           **
 *********************************************************)

(*
 * Replaces a variable in an expression with a target expression.
 * Respects scope by not replacing into "let" expressions which
 * bind a variable of the same name.
 *
 * ex     - the expression to replace in
 * target - the variable to search for
 * repl   - the replacement expression
 *
 * Returns:
 * the resulting exp with all proper replacements
 *)
let rec replace_in_exp (ex : L4_ast.exp) (target : L4_ast.var) (repl : L4_ast.exp) : L4_ast.exp =
   match ex with
   | LetExp(p,v,e1,e2) ->
      (* if this let binds a variable with same name as target, don't replace in the body
       * (i.e. preserve scope) *)
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
      if (ts <> s) then ex else repl
   | IntExp(_,_) -> ex
   | LabelExp(_,_) -> ex
;;

(* 
 * Recombines an extracted expression back with it's old environment.
 * (this is used after a lift_one operation)
 *
 * e2 - the expression environment (i.e. the remainder after extraction)
 * extr - the list of (x,e) pairs extracted, where x is the
 *        uniquely-generated variable, and e is an extracted exp
 * 
 * Returns:
 * the resultant exp
*)
let rec recombine_exp (e2 : L4_ast.exp) (extr : (L4_ast.var * L4_ast.exp) list) : (L4_ast.exp) =
   match extr with
   | [] -> e2
   | (x,extracted)::more ->
      let env = recombine_exp e2 more in
      (match extracted with
      | LetExp(p,v,e1,e2) -> 
         let cv = Var(p,get_unique_symbol l4_prefix) in
         L4_ast.LetExp(p,cv,e1,LetExp(p,x,(replace_in_exp e2 v (VarExp(p,cv))),env))
      | IfExp(p,e1,e2,e3) -> L4_ast.IfExp(p,e1,replace_in_exp env x e2,replace_in_exp env x e3)
      | BeginExp(p,e1,e2) ->    
         let cv = Var(p,get_unique_symbol l4_prefix) in
         L4_ast.LetExp(p,cv,e1,L4_ast.LetExp(p,x,e2,env)) 
      | AppExp(p,e,el) -> L4_ast.LetExp(p,x,extracted,env) 
      | NewArrayExp(p,e1,e2) -> L4_ast.LetExp(p,x,extracted,env) 
      | NewTupleExp(p,el) -> L4_ast.LetExp(p,x,extracted,env) 
      | ArefExp(p,e1,e2) -> L4_ast.LetExp(p,x,extracted,env) 
      | AsetExp(p,e1,e2,e3) -> L4_ast.LetExp(p,x,extracted,env) 
      | AlenExp(p,e1) -> L4_ast.LetExp(p,x,extracted,env) 
      | PrintExp(p,e) -> L4_ast.LetExp(p,x,extracted,env) 
      | MakeClosureExp(p,s,e) -> L4_ast.LetExp(p,x,extracted,env) 
      | ClosureProcExp(p,e) -> L4_ast.LetExp(p,x,extracted,env) 
      | ClosureVarsExp(p,e) -> L4_ast.LetExp(p,x,extracted,env) 
      | PlusExp(p,e1,e2) -> L4_ast.LetExp(p,x,extracted,env) 
      | MinusExp(p,e1,e2) -> L4_ast.LetExp(p,x,extracted,env) 
      | TimesExp(p,e1,e2) -> L4_ast.LetExp(p,x,extracted,env) 
      | LtExp(p,e1,e2) -> L4_ast.LetExp(p,x,extracted,env) 
      | LeqExp(p,e1,e2) -> L4_ast.LetExp(p,x,extracted,env) 
      | EqExp(p,e1,e2) -> L4_ast.LetExp(p,x,extracted,env) 
      | NumberPredExp(p,e) -> L4_ast.LetExp(p,x,extracted,env) 
      | ArrayPredExp(p,e) -> L4_ast.LetExp(p,x,extracted,env)
      | VarExp(p,s) -> L4_ast.LetExp(p,x,extracted,env) 
      | IntExp(p,i) -> L4_ast.LetExp(p,x,extracted,env) 
      | LabelExp(p,s) -> L4_ast.LetExp(p,x,extracted,env) )
;;

type environment = ExpEnv | DExpEnv | SValEnv;;

(*
 * Lifts the next-evaluated subexpression out of an expression.
 * (this is used before a recombine_exp operation)
 *
 * e  - the expression under consideration
 * et - which type of environment this expression is to be used in
 *      (one of ExpEnv, DExpEnv, SValEnv)
 *
 * Returns a pair (xe,env) where
 * xe  - a list of (x,e2) where x is a variable and e2 is its value
 * env - the remainder of the expression, with x's inserted appropriately
 *)
let rec lift_one (e : L4_ast.exp) (en : environment) (flatten_tuples : bool) :
                           ((L4_ast.var * L4_ast.exp) list * L4_ast.exp) =
   match e with
   | LetExp(p,v,e1,e2) -> 
      let (pull1,env1) = lift_one e1 DExpEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,LetExp(p,v,env1,e2)) else (
      match en with
      | ExpEnv -> ([],e) 
      | _ ->
         let v2 = L4_ast.Var(p,get_unique_symbol l4_prefix) in
         let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(v2,e1);(uv,(replace_in_exp e2 v (VarExp(p,v2))))], VarExp(p,uv)) )
   | IfExp(p,e1,e2,e3) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,IfExp(p,env1,e2,e3)) else (
      match en with
      | ExpEnv -> ([],e) 
      | _ -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv)) )
   | BeginExp(p,e1,e2) -> 
      let (pull1,env1) = lift_one e1 DExpEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,BeginExp(p,env1,e2)) else (
      match en with
      | ExpEnv -> ([],e)
      | _ -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv)) )
   | AppExp(p,ex,el) -> 
      let (pull1,env1) = lift_one ex SValEnv flatten_tuples in
      let (pull2,env2,b) = List.fold_left (fun (pull2,env2,b) e ->
            let (pull3,env3) = lift_one e SValEnv flatten_tuples in
            if b then (pull2,env2@[e],b) else
            if List.length pull3 > 0 then (pull3,env2@[env3],true) else
            (pull2,env2@[e],b)
      ) ([],[],false) el in
      if List.length pull1 > 0 then (pull1,AppExp(p,env1,el)) else
      if List.length pull2 > 0 then (pull2,AppExp(p,ex,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | NewArrayExp(p,e1,e2) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      let (pull2,env2) = lift_one e2 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,NewArrayExp(p,env1,e2)) else
      if List.length pull2 > 0 then (pull2,NewArrayExp(p,e1,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | NewTupleExp(p,el) -> 
      let (pull2,env2,b) = List.fold_left (fun (pull2,env2,b) e ->
            let (pull3,env3) = lift_one e (if flatten_tuples then SValEnv else DExpEnv) flatten_tuples in
            if b then (pull2,env2@[e],b) else
            if List.length pull3 > 0 then (pull3,env2@[env3],true) else
            (pull2,env2@[e],b)
      ) ([],[],false) el in
      if List.length pull2 > 0 then (pull2,NewTupleExp(p,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | ArefExp(p,e1,e2) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      let (pull2,env2) = lift_one e2 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,ArefExp(p,env1,e2)) else
      if List.length pull2 > 0 then (pull2,ArefExp(p,e1,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | AsetExp(p,e1,e2,e3) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      let (pull2,env2) = lift_one e2 SValEnv flatten_tuples in
      let (pull3,env3) = lift_one e3 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,AsetExp(p,env1,e2,e3)) else
      if List.length pull2 > 0 then (pull2,AsetExp(p,e1,env2,e3)) else
      if List.length pull3 > 0 then (pull3,AsetExp(p,e1,e2,env3)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | AlenExp(p,e1) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,AlenExp(p,env1)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | PrintExp(p,e1) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,PrintExp(p,env1)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | MakeClosureExp(p,s,e1) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,MakeClosureExp(p,s,env1)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | ClosureProcExp(p,e1) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,ClosureProcExp(p,env1)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | ClosureVarsExp(p,e1) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,ClosureVarsExp(p,env1)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | PlusExp(p,e1,e2) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      let (pull2,env2) = lift_one e2 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,PlusExp(p,env1,e2)) else
      if List.length pull2 > 0 then (pull2,PlusExp(p,e1,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | MinusExp(p,e1,e2) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      let (pull2,env2) = lift_one e2 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,MinusExp(p,env1,e2)) else
      if List.length pull2 > 0 then (pull2,MinusExp(p,e1,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | TimesExp(p,e1,e2) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      let (pull2,env2) = lift_one e2 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,TimesExp(p,env1,e2)) else
      if List.length pull2 > 0 then (pull2,TimesExp(p,e1,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | LtExp(p,e1,e2) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      let (pull2,env2) = lift_one e2 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,LtExp(p,env1,e2)) else
      if List.length pull2 > 0 then (pull2,LtExp(p,e1,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | LeqExp(p,e1,e2) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      let (pull2,env2) = lift_one e2 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,LeqExp(p,env1,e2)) else
      if List.length pull2 > 0 then (pull2,LeqExp(p,e1,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | EqExp(p,e1,e2) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      let (pull2,env2) = lift_one e2 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,EqExp(p,env1,e2)) else
      if List.length pull2 > 0 then (pull2,EqExp(p,e1,env2)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | NumberPredExp(p,e1) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,NumberPredExp(p,env1)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | ArrayPredExp(p,e1) -> 
      let (pull1,env1) = lift_one e1 SValEnv flatten_tuples in
      if List.length pull1 > 0 then (pull1,ArrayPredExp(p,env1)) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_symbol l4_prefix) in
             ([(uv,e)], VarExp(p,uv))
      | _ -> ([],e) )
   | VarExp(p,s) ->    ([],e)
   | IntExp(p,i) ->    ([],e)
   | LabelExp(p,s) ->  ([],e)
;;

(*
 * Puts an L4 expression into L3 form.
 * (the expression must then be cast to L3 types
 * using compile_exp)
 *)
let rec normalize_exp (the_exp : L4_ast.exp) (flatten_tuples : bool) : L4_ast.exp =
      let (pull,env) = lift_one the_exp ExpEnv flatten_tuples in
      match pull with
      | [] -> (
        match env with
        | LetExp(p,v,e1,e2) -> LetExp(p,v,e1,normalize_exp e2 flatten_tuples)
        | IfExp(p,e1,e2,e3) -> IfExp(p,e1,normalize_exp e2 flatten_tuples,normalize_exp e3 flatten_tuples)
        | BeginExp(p,e1,e2) -> BeginExp(p,e1,normalize_exp e2 flatten_tuples)
        | _ -> env )
      | _ -> recombine_exp (normalize_exp env flatten_tuples) pull
;;

(*
 * These functions compile a (normalized) L4 program into an L3 program
 *)

let rec compile_program (pr : L4_ast.program) (flatten_tuples : bool) : L3_ast.program =
   match pr with
   | Program(p,e,fl) ->
      let start_time = Sys.time () in
      if !debug_4 || !verbose_mode then (
         print_string ("Compiling L4 to L3..."^(if !verbose_mode then " " else "\n"));
         flush Pervasives.stdout
      );
      let e2 = compile_exp e flatten_tuples in
      let fl2 = List.map (fun f -> compile_func f flatten_tuples) fl in
      if !debug_4 || !verbose_mode then (
         let diff = (Sys.time ()) -. start_time in
         print_string ((if !verbose_mode then "" else "...")^"done"^
            (if !verbose_mode then "" else " with L4->L3")^": "^(string_of_float diff)^" sec.\n");
         flush Pervasives.stdout
      );
      L3_ast.Program(p,e2,fl2)

and compile_func (f : L4_ast.func) (flatten_tuples : bool) : L3_ast.func =
   match f with
   | Function(p,name,vl,e) -> L3_ast.Function(p, name, List.map (fun v -> compile_var v) vl, compile_exp e flatten_tuples)

and compile_exp (e : L4_ast.exp) (flatten_tuples : bool) : L3_ast.exp = 
   let the_exp = normalize_exp e flatten_tuples in
   match the_exp with
   | LetExp(p,v,e1,e2) -> L3_ast.LetExp(p,compile_var v,compile_exp_to_dexp e1,compile_exp e2 flatten_tuples)
   | IfExp(p,e1,e2,e3) -> L3_ast.IfExp(p,compile_exp_to_sval e1,compile_exp e2 flatten_tuples,compile_exp e3 flatten_tuples)
   | AppExp(p,e,el) ->
      L3_ast.DExpExp(p,L3_ast.AppDExp(p,compile_exp_to_sval e, List.map (fun e -> compile_exp_to_sval e) el))
   | NewArrayExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.NewArrayDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2))
   | NewTupleExp(p,el) ->
      L3_ast.DExpExp(p,L3_ast.NewTupleDExp(p,List.map (fun e -> compile_exp_to_dexp e) el))
   | ArefExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.ArefDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2))
   | AsetExp(p,e1,e2,e3) ->
      L3_ast.DExpExp(p,L3_ast.AsetDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2,compile_exp_to_sval e3))
   | AlenExp(p,e1) -> L3_ast.DExpExp(p,L3_ast.AlenDExp(p,compile_exp_to_sval e1))
   | BeginExp(p,e1,e2) ->
      let v = L3_ast.Var(p,get_unique_symbol l4_prefix) in
      L3_ast.LetExp(p,v,compile_exp_to_dexp e1,compile_exp e2 flatten_tuples)
   | PrintExp(p,e) -> L3_ast.DExpExp(p,L3_ast.PrintDExp(p,compile_exp_to_sval e)) 
   | MakeClosureExp(p,s,e) -> L3_ast.DExpExp(p,L3_ast.MakeClosureDExp(p,s,compile_exp_to_sval e))
   | ClosureProcExp(p,e) -> L3_ast.DExpExp(p,L3_ast.ClosureProcDExp(p,compile_exp_to_sval e))
   | ClosureVarsExp(p,e) -> L3_ast.DExpExp(p,L3_ast.ClosureVarsDExp(p,compile_exp_to_sval e))
   | PlusExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.PlusDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2))
   | MinusExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.MinusDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2)) 
   | TimesExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.TimesDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2)) 
   | LtExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.LtDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2)) 
   | LeqExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.LeqDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2)) 
   | EqExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.EqDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2)) 
   | NumberPredExp(p,e) -> L3_ast.DExpExp(p,L3_ast.NumberPredDExp(p,compile_exp_to_sval e)) 
   | ArrayPredExp(p,e) -> L3_ast.DExpExp(p,L3_ast.ArrayPredDExp(p,compile_exp_to_sval e)) 
   | VarExp(p,v) -> L3_ast.DExpExp(p,L3_ast.SValDExp(p,L3_ast.VarSVal(p,compile_var v))) 
   | IntExp(p,i) -> L3_ast.DExpExp(p,L3_ast.SValDExp(p,L3_ast.IntSVal(p,i))) 
   | LabelExp(p,s) -> L3_ast.DExpExp(p,L3_ast.SValDExp(p,L3_ast.LabelSVal(p,s)))

and compile_exp_to_dexp (e : L4_ast.exp) : L3_ast.dexp =
   match e with
   | AppExp(p,e,el) -> L3_ast.AppDExp(p,compile_exp_to_sval e, List.map (fun ex -> compile_exp_to_sval ex) el)
   | NewArrayExp(p,e1,e2) -> L3_ast.NewArrayDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | NewTupleExp(p,el) -> L3_ast.NewTupleDExp(p,List.map (fun ex -> compile_exp_to_dexp ex) el)
   | ArefExp(p,e1,e2) -> L3_ast.ArefDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2)
   | AsetExp(p,e1,e2,e3) -> L3_ast.AsetDExp(p,compile_exp_to_sval e1, compile_exp_to_sval e2,compile_exp_to_sval e3)
   | AlenExp(p,e) -> L3_ast.AlenDExp(p,compile_exp_to_sval e)
   | PrintExp(p,e) -> L3_ast.PrintDExp(p,compile_exp_to_sval e)
   | MakeClosureExp(p,s,e) -> L3_ast.MakeClosureDExp(p,s,compile_exp_to_sval e)
   | ClosureProcExp(p,e) -> L3_ast.ClosureProcDExp(p,compile_exp_to_sval e)
   | ClosureVarsExp(p,e) -> L3_ast.ClosureVarsDExp(p,compile_exp_to_sval e)
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
   | _ -> print_exp e; die_system_error " : expected a dexp" (* TODO - clean up these error messages *)

and compile_exp_to_sval (e : L4_ast.exp) : L3_ast.sval =
   match e with
   | VarExp(p,v) -> L3_ast.VarSVal(p,compile_var v)
   | IntExp(p,i) -> L3_ast.IntSVal(p,i)
   | LabelExp(p,s) -> L3_ast.LabelSVal(p,s)
   | _ -> print_exp e; die_system_error " : expected an sval" (* TODO - clean up these error messages *)

and compile_var (v : L4_ast.var) : L3_ast.var =
   match v with
   | Var(p,s) -> L3_ast.Var(p,s)
;;
