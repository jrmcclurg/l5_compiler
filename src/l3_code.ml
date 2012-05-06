(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/7/2012
 *
 * L3-to-L2 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l3_code.ml
 * Contains the l3-to-l2 compilation
 * functionality.
 *)

open L3_ast;;
open Utils;;

(*********************************************************
 **  L3-to-L2 CODE GENERATION                           **
 *********************************************************)

(* compile an L2 program into an L1 program *)

let rec compile_program (p : L3_ast.program) : L2_ast.program =
   match p with
   | Program(p,e,fl) -> 
      (* compile all the functions into L1 functions, giving
       * each one a unique count (starting with 0) *)
      let (_,fl2) = List.fold_left (fun (count,res) f ->
         (count+1,res@[compile_func f (get_unique_varname l3_prefix count)])
      ) (1,[]) fl in (* start with the unique id "1", since we use "0" for
                      * the exp "e" *)
      let main = (L2_ast.Function(p,None,compile_exp e (get_unique_varname l3_prefix 0))) in
      L2_ast.Program(p, main::fl2)
and compile_func (f : L3_ast.func) (prefix : string) : L2_ast.func = 
   match f with
   | Function(p,name,vl,e) ->
      let prefix2 = get_unique_varname l3_prefix 0 in
      let regs = [L2_ast.EcxReg(p);L2_ast.EdxReg(p);L2_ast.EaxReg(p)] in
      if ((List.length vl) > 3) then die_error p "more than 3 function args";
      let (_,il1) = List.fold_left (fun (k,res) v ->
         let reg = List.nth regs k in
         let i = L2_ast.AssignInstr(p,compile_var v prefix2,L2_ast.VarSVal(p,reg)) in
         (k+1, res@[i])
      ) (0,[]) vl in
      let il2 = compile_exp e (get_unique_varname l3_prefix 1) in
      L2_ast.Function(p, Some(name), il1@il2)
and compile_exp (e : L3_ast.exp) (prefix : string) : L2_ast.instr list = 
   match e with
   | LetExp(p,v,de,e) ->
      let v2 = compile_var v (get_unique_varname prefix 0) in
      (compile_dexp de v2 (get_unique_varname prefix 1))@
      (compile_exp e (get_unique_varname prefix 2))
   | _ -> [] (* TODO XXX *)
and compile_dexp (de : L3_ast.dexp) (dest : L2_ast.var) (prefix : string) : L2_ast.instr list = 
   match de with
   | PrintDExp(p,sv) -> [L2_ast.PrintInstr(p,L2_ast.IntTVal(p,123L));L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,L2_ast.EaxReg(p)))]
   | _ -> [] (* TODO XXX *)
and compile_var (v : L3_ast.var) (prefix : string) : L2_ast.var = 
   match v with
   | Var(p,raw) ->
   (* TODO XXX - this should actually be in the L3-to-L2 compilation *)
   let resvd = ["esi";"edi";"ebp";"esp";"eax";"ecx";"edx";"ebx";
                "array-error";"tail-call";"allocate";"return";"cjump";"goto";"mem";"call"] in
   let name = (try (concat_unique_names prefix (List.find (fun x -> (x = raw)) resvd))
               with _ -> raw) in
   L2_ast.Var(p,name)
