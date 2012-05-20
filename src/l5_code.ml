(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/21/2012
 *
 * L5-to-L4 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l4_code.ml
 * Contains the l5-to-l4 compilation
 * functionality.
 *)

open L5_ast;;
open Utils;;

(*********************************************************
 **  L5-to-L4 CODE GENERATION                           **
 *********************************************************)

(*
 * These functions compile an L5 program into an L4 program
 *)

let rec compile_program (pr : L5_ast.program) : L4_ast.program =
   match pr with
   | Program(p,e) -> 
      let (e2,fl) = compile_exp e in
      L4_ast.Program(p,e2,fl)

and compile_exp (e : L5_ast.exp) : (L4_ast.exp * L4_ast.func list) =
   match e with
   | LambdaExp(p,vl,e) -> 
      let name = get_unique_ident l5_prefix in
      let fparam = get_unique_ident l5_prefix in
      let bparam = get_unique_ident l5_prefix in
      let free_vars = [Var(p,"m1");Var(p,"m2")] in (*get_free_vars e vl in*)
      let (e2,fl) = compile_exp e in
      let (e3,_) = List.fold_right (fun v (ex,k) ->
         (L4_ast.LetExp(p,compile_var v,L4_ast.ArefExp(p,L4_ast.VarExp(p,L4_ast.Var(p,bparam)),
                                           L4_ast.IntExp(p,Int64.of_int k)),ex), k-1)
      ) vl (e2,(List.length vl)-1) in
      let (e4,_) = List.fold_right (fun v (ex,k) ->
         (L4_ast.LetExp(p,compile_var v,L4_ast.ArefExp(p,L4_ast.VarExp(p,L4_ast.Var(p,fparam)),
                                           L4_ast.IntExp(p,Int64.of_int k)),ex), k-1)
      ) free_vars (e3,(List.length free_vars)-1) in
      (L4_ast.MakeClosureExp(p,name,L4_ast.NewTupleExp(p,List.map (fun f -> L4_ast.VarExp(p,compile_var f)) free_vars)),
       (L4_ast.Function(p,name,[L4_ast.Var(p,fparam);L4_ast.Var(p,bparam)],e4))::fl)
   | VarExp(p,v) -> (L4_ast.VarExp(p,compile_var v), [])
   | LetExp(p,v,e1,e2) ->
      let (e1n,fl1) = compile_exp e1 in
      let (e2n,fl2) = compile_exp e2 in
      (L4_ast.LetExp(p,compile_var v,e1n,e2n),fl1@fl2)
   | IfExp(p,e1,e2,e3) ->
      let (e1n,fl1) = compile_exp e1 in
      let (e2n,fl2) = compile_exp e2 in
      let (e3n,fl3) = compile_exp e3 in
      (L4_ast.IfExp(p,e1n,e2n,e3n),fl1@fl2@fl3)
   | NewTupleExp(p,el) ->
      let (el2,fl) = List.fold_left (fun (elx,flx) ex ->
         let (et,flt) = compile_exp ex in
         (elx@[et], flx@flt)
      ) ([],[]) el in
      (L4_ast.NewTupleExp(p,el2),fl)
   | BeginExp(p,e1,e2) -> 
      let (e1n,fl1) = compile_exp e1 in
      let (e2n,fl2) = compile_exp e2 in
      (L4_ast.BeginExp(p,e1n,e2n),fl1@fl2)
   | AppExp(p,e,el) -> 
      let name = get_unique_ident l5_prefix in
      let (e2,fl1) = compile_exp e in
      let (el2,fl2) = List.fold_left (fun (elx,flx) ex ->
         let (et,flt) = compile_exp ex in
         (elx@[et], flx@flt)
      ) ([],[]) el in
      let f = L4_ast.Var(p,name) in
      (L4_ast.LetExp(p,f,e2,L4_ast.AppExp(p,L4_ast.ClosureProcExp(p,L4_ast.VarExp(p,f)),
         [L4_ast.ClosureVarsExp(p,L4_ast.VarExp(p,f));L4_ast.NewTupleExp(p,el2)])),fl1@fl2)
   (*| PrimExp(p,pr) -> *)
   | IntExp(p,i) -> (L4_ast.IntExp(p,i), [])
and compile_var (v : L5_ast.var) : L4_ast.var = 
   match v with
   | Var(p,s) -> L4_ast.Var(p,s)
;;
