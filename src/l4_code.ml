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
      if (ts <> s) then ex else repl
   | IntExp(_,_) -> ex
   | LabelExp(_,_) -> ex
;;

(*let get_let (extr : (L4_ast.var * L4_ast.exp) list) (e : l4_ast.exp) : L4_ast.exp =
   match extr with
   | [] -> e
   | (x,extracted)::more -> L4_ast.LetExp(p,x,extracted,get_let more e)
;;*)

(* 
 * Where e is an expression with the extraction site labeled with x,
 * and bad is the thing to extract (b,x are returned by check_extraction)
*)
let rec flatten_exp (e2 : L4_ast.exp) (extr : (L4_ast.var * L4_ast.exp) list) : (L4_ast.exp) =
   (*print_string "Flattening:\n   env = ";
   print_exp e2;
   List.iter (fun (x,e3) ->
      print_string "\n   extr = (";
      print_var x;
      print_string ", ";
      print_exp e3;
      print_string ")";
   ) extr;
   print_string "\n";*)
   match extr with
   | [] -> e2
   | (x,extracted)::more ->
      let env = flatten_exp e2 more in
      (match extracted with
      (*| LetExp(p,v,e1,e2) -> L4_ast.LetExp(p,x,e1,replace_in_exp (replace_in_exp e x e2) v (VarExp(p,x)))*)
      | LetExp(p,v,e1,e2) -> 
         let cv = Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #1: ";
         print_var cv;
         print_string "\n";*)
         L4_ast.LetExp(p,cv,e1,LetExp(p,x,(replace_in_exp e2 v (VarExp(p,cv))),env))
      | IfExp(p,e1,e2,e3) ->    L4_ast.IfExp(p,e1,replace_in_exp env x e2,replace_in_exp env x e3)
      | BeginExp(p,e1,e2) ->    
         let cv = Var(p,get_unique_ident l4_prefix) in
         L4_ast.LetExp(p,cv,e1,L4_ast.LetExp(p,x,e2,env)) 
      | AppExp(p,e,el) ->    L4_ast.LetExp(p,x,extracted,env) 
      | NewArrayExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,env) 
      | NewTupleExp(p,el) ->    L4_ast.LetExp(p,x,extracted,env) 
      | ArefExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,env) 
      | AsetExp(p,e1,e2,e3) ->    L4_ast.LetExp(p,x,extracted,env) 
      | AlenExp(p,e1) ->    L4_ast.LetExp(p,x,extracted,env) 
      | PrintExp(p,e) ->    L4_ast.LetExp(p,x,extracted,env) 
      | MakeClosureExp(p,s,e) ->    L4_ast.LetExp(p,x,extracted,env) 
      | ClosureProcExp(p,e) ->    L4_ast.LetExp(p,x,extracted,env) 
      | ClosureVarsExp(p,e) ->    L4_ast.LetExp(p,x,extracted,env) 
      | PlusExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,env) 
      | MinusExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,env) 
      | TimesExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,env) 
      | LtExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,env) 
      | LeqExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,env) 
      | EqExp(p,e1,e2) ->    L4_ast.LetExp(p,x,extracted,env) 
      | NumberPredExp(p,e) ->    L4_ast.LetExp(p,x,extracted,env) 
      | ArrayPredExp(p,e) ->      L4_ast.LetExp(p,x,extracted,env)
      | VarExp(p,s) ->           L4_ast.LetExp(p,x,extracted,env) 
      | IntExp(p,i) ->           L4_ast.LetExp(p,x,extracted,env) 
      | LabelExp(p,s) ->          L4_ast.LetExp(p,x,extracted,env) )
;;

type environment = ExpEnv | DExpEnv | SValEnv;;
let min = 0;;
(* returns created variable, pulled out exp, modified environment, and level *)
let rec lift_one (e : L4_ast.exp) (n : int) (en : environment) :
                           ((L4_ast.var * L4_ast.exp) list * L4_ast.exp * int) =
   match e with
   | LetExp(p,v,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) DExpEnv in
      if num1 > 0 then (pull1,LetExp(p,v,env1,e2),num1) else (
      match en with
      | ExpEnv -> ([],e,0) 
      | _ ->
         let v2 = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #2: ";
         print_var v2;
         print_string "\n";*)
         let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #3: ";
         print_var uv;
         print_string "\n";*)
             ([(v2,e1);(uv,(replace_in_exp e2 v (VarExp(p,v2))))], VarExp(p,uv), n) )
   | IfExp(p,e1,e2,e3) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      if num1 > 0 then (pull1,IfExp(p,env1,e2,e3),num1) else (
      match en with
      | ExpEnv -> ([],e,0) 
      | _ -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #4: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n) )
   | BeginExp(p,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) DExpEnv in
      if num1 > 0 then (pull1,BeginExp(p,env1,e2),num1) else (
      match en with
      | ExpEnv -> ([],e,0)
      | _ -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #5: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n) )
   | AppExp(p,ex,el) -> 
      let (pull1,env1,num1) = lift_one ex (n+1) SValEnv in
      let (pull2,env2,num2,b) = List.fold_left (fun (pull2,env2,num2,b) e ->
            let (pull3,env3,num3) = lift_one e (n+1) SValEnv in
            if b then (pull2,env2@[e],num2,b) else
            if num3 > 0 then (pull3,env2@[env3],num3,true) else
            (pull2,env2@[e],num2,b)
      ) ([],[],0,false) el in
      if num1 > 0 then (pull1,AppExp(p,env1,el),num1) else
      if num2 > 0 then (pull2,AppExp(p,ex,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #6: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | NewArrayExp(p,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      let (pull2,env2,num2) = lift_one e2 (n+1) SValEnv in
      if num1 > 0 then (pull1,NewArrayExp(p,env1,e2),num1) else
      if num2 > 0 then (pull2,NewArrayExp(p,e1,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #7: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | NewTupleExp(p,el) -> 
      (*print_string "Checking in tuple: ";
      print_exp e;
      print_string "\n";*)
      let (pull2,env2,num2,b) = List.fold_left (fun (pull2,env2,num2,b) e ->
            let (pull3,env3,num3) = lift_one e (n+1) SValEnv in
            if b then (pull2,env2@[e],num2,b) else
            if num3 > 0 then (pull3,env2@[env3],num3,true) else
            (pull2,env2@[e],num2,b)
      ) ([],[],0,false) el in
      if num2 > 0 then (pull2,NewTupleExp(p,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #8: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | ArefExp(p,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      let (pull2,env2,num2) = lift_one e2 (n+1) SValEnv in
      if num1 > 0 then (pull1,ArefExp(p,env1,e2),num1) else
      if num2 > 0 then (pull2,ArefExp(p,e1,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #9: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | AsetExp(p,e1,e2,e3) -> 
      (*print_string "Looking at Aset: ";
      print_exp e;
      print_string "\n";*)
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      let (pull2,env2,num2) = lift_one e2 (n+1) SValEnv in
      let (pull3,env3,num3) = lift_one e3 (n+1) SValEnv in
      if num1 > 0 then (pull1,AsetExp(p,env1,e2,e3),num1) else
      if num2 > 0 then (pull2,AsetExp(p,e1,env2,e3),num2) else
      if num3 > 0 then (pull3,AsetExp(p,e1,e2,env3),num3) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #10: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | AlenExp(p,e1) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      if num1 > 0 then (pull1,AlenExp(p,env1),num1) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #11: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | PrintExp(p,e1) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      if num1 > 0 then (pull1,PrintExp(p,env1),num1) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #12: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | MakeClosureExp(p,s,e1) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      if num1 > 0 then (pull1,MakeClosureExp(p,s,env1),num1) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #13: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | ClosureProcExp(p,e1) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      if num1 > 0 then (pull1,ClosureProcExp(p,env1),num1) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #14: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | ClosureVarsExp(p,e1) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      if num1 > 0 then (pull1,ClosureVarsExp(p,env1),num1) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #15: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | PlusExp(p,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      let (pull2,env2,num2) = lift_one e2 (n+1) SValEnv in
      if num1 > 0 then (pull1,PlusExp(p,env1,e2),num1) else
      if num2 > 0 then (pull2,PlusExp(p,e1,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #16: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | MinusExp(p,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      let (pull2,env2,num2) = lift_one e2 (n+1) SValEnv in
      if num1 > 0 then (pull1,MinusExp(p,env1,e2),num1) else
      if num2 > 0 then (pull2,MinusExp(p,e1,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #17: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | TimesExp(p,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      let (pull2,env2,num2) = lift_one e2 (n+1) SValEnv in
      if num1 > 0 then (pull1,TimesExp(p,env1,e2),num1) else
      if num2 > 0 then (pull2,TimesExp(p,e1,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #18: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | LtExp(p,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      let (pull2,env2,num2) = lift_one e2 (n+1) SValEnv in
      if num1 > 0 then (pull1,LtExp(p,env1,e2),num1) else
      if num2 > 0 then (pull2,LtExp(p,e1,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #19: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | LeqExp(p,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      let (pull2,env2,num2) = lift_one e2 (n+1) SValEnv in
      if num1 > 0 then (pull1,LeqExp(p,env1,e2),num1) else
      if num2 > 0 then (pull2,LeqExp(p,e1,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #20: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | EqExp(p,e1,e2) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      let (pull2,env2,num2) = lift_one e2 (n+1) SValEnv in
      if num1 > 0 then (pull1,EqExp(p,env1,e2),num1) else
      if num2 > 0 then (pull2,EqExp(p,e1,env2),num2) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #21: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | NumberPredExp(p,e1) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      if num1 > 0 then (pull1,NumberPredExp(p,env1),num1) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #22: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | ArrayPredExp(p,e1) -> 
      let (pull1,env1,num1) = lift_one e1 (n+1) SValEnv in
      if num1 > 0 then (pull1,ArrayPredExp(p,env1),num1) else (
      match en with
      | SValEnv -> let uv = L4_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #23: ";
         print_var uv;
         print_string "\n";*)
             ([(uv,e)], VarExp(p,uv), n)
      | _ -> ([],e,0) )
   | VarExp(p,s) ->    ([],e,0)
   | IntExp(p,i) ->    ([],e,0)
   | LabelExp(p,s) ->  ([],e,0)
;;

(* puts an L4 program into L3 form *)
let rec normalize_exp (the_exp : L4_ast.exp) : L4_ast.exp =
      (*print_string "Normalizing: ";
      print_exp the_exp;
      print_string "\n";*)
      let (pull,env,i) = lift_one the_exp 0 ExpEnv in
      match pull with
      | [] -> (
        match env with
        | LetExp(p,v,e1,e2) -> LetExp(p,v,e1,normalize_exp e2)
        | IfExp(p,e1,e2,e3) -> IfExp(p,e1,normalize_exp e2,normalize_exp e3)
        | BeginExp(p,e1,e2) -> BeginExp(p,e1,normalize_exp e2)
        | _ -> env 
        )
      | _ ->
      (*print_string "  Returned env: ";
      print_exp env;
      print_string "\n";
      List.iter (fun (x,e) ->
         print_string "  Pulled out: (";
         print_var x;
         print_string ", ";
         print_exp e;
         print_string ")\n";
      ) pull;*)
      let n = normalize_exp env in
      (*print_string "Normalized: ";
      print_exp n;
      print_string "\n";*)
      let f = flatten_exp n pull in
      (*print_string "Received: ";
      print_exp the_exp;
      print_string "\n";
      print_string "Flattened: ";
      print_exp f;
      print_string "\n";*)
      f
;;

(* compile an L4 program into an L3 program *)
(* the program must be normalized first, or runtime errors will occur *)

let rec compile_program (pr : L4_ast.program) : L3_ast.program =
   match pr with
   | Program(p,e,fl) -> L3_ast.Program(p,compile_exp e,List.map (fun f -> compile_func f) fl)

and compile_func (f : L4_ast.func) : L3_ast.func =
   match f with
   | Function(p,name,vl,e) -> L3_ast.Function(p, name, List.map (fun v -> compile_var v) vl, compile_exp e)

and compile_exp (e : L4_ast.exp) : L3_ast.exp = 
   (*L3_ast.DExpExp(NoPos,L3_ast.SValDExp(NoPos,L3_ast.IntSVal(NoPos,0L)));*)
   let the_exp = normalize_exp e in
   match the_exp with
   | LetExp(p,v,e1,e2) -> L3_ast.LetExp(p,compile_var v,compile_exp_to_dexp e1,compile_exp e2)
   | IfExp(p,e1,e2,e3) -> L3_ast.IfExp(p,compile_exp_to_sval e1,compile_exp e2,compile_exp e3)
   | AppExp(p,e,el) ->
      L3_ast.DExpExp(p,L3_ast.AppDExp(p,compile_exp_to_sval e, List.map (fun e -> compile_exp_to_sval e) el))
   | NewArrayExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.NewArrayDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2))
   | NewTupleExp(p,el) ->
      L3_ast.DExpExp(p,L3_ast.NewTupleDExp(p,List.map (fun e -> compile_exp_to_sval e) el))
   | ArefExp(p,e1,e2) -> L3_ast.DExpExp(p,L3_ast.ArefDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2))
   | AsetExp(p,e1,e2,e3) ->
      L3_ast.DExpExp(p,L3_ast.AsetDExp(p,compile_exp_to_sval e1,compile_exp_to_sval e2,compile_exp_to_sval e3))
   | AlenExp(p,e1) -> L3_ast.DExpExp(p,L3_ast.AlenDExp(p,compile_exp_to_sval e1))
   | BeginExp(p,e1,e2) ->
      let v = L3_ast.Var(p,get_unique_ident l4_prefix) in
         (*print_string "generating unique #24: ";
         L3_ast.print_var v;
         print_string "\n";*)
      L3_ast.LetExp(p,v,compile_exp_to_dexp e1,compile_exp e2)
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
   | NewTupleExp(p,el) -> L3_ast.NewTupleDExp(p,List.map (fun ex -> compile_exp_to_sval ex) el)
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
