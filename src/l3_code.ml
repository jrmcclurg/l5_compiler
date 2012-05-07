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
      let main = (L2_ast.Function(p,None,compile_exp e true (get_unique_varname l3_prefix 0))) in
      L2_ast.Program(p, main::fl2)
and compile_func (f : L3_ast.func) (prefix : string) : L2_ast.func = 
   match f with
   | Function(p,name,vl,e) ->
      let regs = [L2_ast.EcxReg(p);L2_ast.EdxReg(p);L2_ast.EaxReg(p)] in
      if ((List.length vl) > 3) then die_error p "more than 3 function args";
      let (_,il1) = List.fold_left (fun (k,res) v ->
         let reg = List.nth regs k in
         let i = L2_ast.AssignInstr(p,compile_var v,L2_ast.VarSVal(p,reg)) in
         (k+1, res@[i])
      ) (0,[]) vl in
      let il2 = compile_exp e false (get_unique_varname prefix 1) in
      L2_ast.Function(p, Some(name), il1@il2)
and compile_exp (e : L3_ast.exp) (first : bool) (prefix : string) : L2_ast.instr list = 
   match e with
   | LetExp(p,v,de,e) ->
      (* generate the L2 variable *)
      let v2 = compile_var v in
      (* compile the "d" and store the result in the compiled var *)
      (compile_dexp de v2 false (get_unique_varname prefix 0))@
      (* compile the "e" *)
      (compile_exp e first (get_unique_varname prefix 1))
   | IfExp(p,sv,e1,e2) ->
      let tv = L2_ast.get_tval (compile_sval sv) in
      let il1 = (compile_exp e1 first (get_unique_varname prefix 0)) in
      let il2 = (compile_exp e2 first (get_unique_varname prefix 1)) in
      let tl = get_unique_varname prefix 2 in
      let fl = get_unique_varname prefix 3 in
      let jl = get_unique_varname prefix 4 in
      let i = L2_ast.EqJumpInstr(p,tv,L2_ast.IntTVal(p,1L),fl,tl) in
      i::(L2_ast.LabelInstr(p,tl))::il1@
      [L2_ast.GotoInstr(p,jl);L2_ast.LabelInstr(p,fl)]
      @il2@[L2_ast.LabelInstr(p,jl);
      (* we put the (eax <- eax) instruction at the end, because the L2
       * interpreter complains about functions ending with a label *)
      L2_ast.AssignInstr(p,L2_ast.EaxReg(p),L2_ast.VarSVal(p,L2_ast.EaxReg(p)))]
   | DExpExp(p,de) -> 
      let tail = (not first) in
      (compile_dexp de (L2_ast.EaxReg(p)) tail (get_unique_varname prefix 0))@
      (if first then [] else [L2_ast.ReturnInstr(p)]) (* only add (return) instr in main function *)
and compile_dexp (de : L3_ast.dexp) (dest : L2_ast.var) (tail : bool) (prefix : string) : L2_ast.instr list = 
   match de with
   | PlusDExp(p,sv1,sv2) ->
      (* (2a+1)+(2b+1)-1 = 2a+1+2b+1-1 = 2a+2b+1 = 2(a+b)+1  *)
      let sv1t = compile_sval sv1 in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.AssignInstr(p,dest,sv1t);
       L2_ast.PlusInstr(p,dest,tv2);
       L2_ast.MinusInstr(p,dest,L2_ast.IntTVal(p,1L))]
   | MinusDExp(p,sv1,sv2) ->
      (* (2a+1)-(2b+1)+1 = 2a+1-2b-1+1 = 2a-2b+1 = 2(a-b)+1  *)
      let sv1t = compile_sval sv1 in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.AssignInstr(p,dest,sv1t);
       L2_ast.MinusInstr(p,dest,tv2);
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1L))]
   | TimesDExp(p,sv1,sv2) ->
      (* ((2a+1)*(2b+1)+3-(2a+1)-(2b+1)) >> 1 =
         (4ab+2a+2b+1 +1+2-(2a+1)-(2b+1))>>1 = 2(2ab+1)>>1 = 2ab+1 *)
      let sv1t = compile_sval sv1 in
      let tv1 = L2_ast.get_tval sv1t in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.AssignInstr(p,dest,sv1t);
       L2_ast.TimesInstr(p,dest,tv2);
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,3L));
       L2_ast.MinusInstr(p,dest,tv1);
       L2_ast.MinusInstr(p,dest,tv2);
       L2_ast.SrlInstr(p,dest,L2_ast.IntShVal(p,1L))]
   | LtDExp(p,sv1,sv2) ->
      let tv1 = L2_ast.get_tval (compile_sval sv1) in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.LtInstr(p,dest,tv1,tv2);
       L2_ast.SllInstr(p,dest,L2_ast.IntShVal(p,1L));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1L))]
   | LeqDExp(p,sv1,sv2) ->
      let tv1 = L2_ast.get_tval (compile_sval sv1) in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.LeqInstr(p,dest,tv1,tv2);
       L2_ast.SllInstr(p,dest,L2_ast.IntShVal(p,1L));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1L))]
   | EqDExp(p,sv1,sv2) ->
      let tv1 = L2_ast.get_tval (compile_sval sv1) in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.EqInstr(p,dest,tv1,tv2);
       L2_ast.SllInstr(p,dest,L2_ast.IntShVal(p,1L));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1L))]
   | NumberPredDExp(p,sv) ->
      let sv1t = compile_sval sv in
      [L2_ast.AssignInstr(p,dest,sv1t);
       L2_ast.BitAndInstr(p,dest,L2_ast.IntTVal(p,1L));
       L2_ast.SllInstr(p,dest,L2_ast.IntShVal(p,1L));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1L))]
   | ArrayPredDExp(p,sv) ->
      let sv1t = compile_sval sv in
      [L2_ast.AssignInstr(p,dest,sv1t);
       L2_ast.BitAndInstr(p,dest,L2_ast.IntTVal(p,1L));
       L2_ast.TimesInstr(p,dest,L2_ast.IntTVal(p,-2L));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,3L))]
   | AppDExp(p,sv,svl) ->
      let regs = [L2_ast.EcxReg(p);L2_ast.EdxReg(p);L2_ast.EaxReg(p)] in
      if ((List.length svl) > 3) then die_error p "more than 3 function args";
      let (_,il1) = List.fold_left (fun (k,res) v ->
         let reg = List.nth regs k in
         let i = L2_ast.AssignInstr(p,reg,compile_sval v) in
         (k+1, res@[i])
      ) (0,[]) svl in
      let uv = L2_ast.get_uval (compile_sval sv) in
      il1@(if tail then [L2_ast.TailCallInstr(p,uv)] else [L2_ast.CallInstr(p,uv)])@
      [L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,L2_ast.EaxReg(p)))]
   | NewArrayDExp(p,sv1,sv2) ->
      let tv1 = L2_ast.get_tval (compile_sval sv1) in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.AllocInstr(p,tv1,tv2);L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,L2_ast.EaxReg(p)))]
   | NewTupleDExp(p,svl) ->
      let len = List.length svl in
      let (_,l2) = List.fold_left (fun (off,res) sv ->
         ((off+4),res@[L2_ast.MemWriteInstr(p,dest,Int64.of_int off,compile_sval sv)])
      ) (4,[]) svl in
      [L2_ast.AllocInstr(p,L2_ast.IntTVal(p,Int64.of_int (2*len+1)),L2_ast.IntTVal(p,0L));
       L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,L2_ast.EaxReg(p)))]@
      l2
   | ArefDExp(p,sv1,sv2) ->
      let sv1t = (compile_sval sv1) in
      let tv1 = L2_ast.get_tval sv1t in
      let sv2t = (compile_sval sv2) in
      let tmp = L2_ast.Var(p,get_unique_varname prefix 0) in
      let tl1 = get_unique_varname prefix 1 in
      let tl2 = get_unique_varname prefix 2 in
      let fl = get_unique_varname prefix 3 in
      [L2_ast.AssignInstr(p,dest,sv2t);
       L2_ast.SrlInstr(p,dest,L2_ast.IntShVal(p,1L));
       L2_ast.MemReadInstr(p,tmp,L2_ast.get_var sv1t,0L);
       L2_ast.LtJumpInstr(p,L2_ast.VarTVal(p,dest),L2_ast.VarTVal(p,tmp),tl1,fl);
       L2_ast.LabelInstr(p,fl); (* fail label *)
       L2_ast.SllInstr(p,dest,L2_ast.IntShVal(p,1L));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1L));
       L2_ast.ArrayErrorInstr(p,tv1,L2_ast.VarTVal(p,dest));
       L2_ast.LabelInstr(p,tl1); (* success label 1 *)
       L2_ast.LtJumpInstr(p,L2_ast.VarTVal(p,dest),L2_ast.IntTVal(p,0L),fl,tl2);
       L2_ast.LabelInstr(p,tl2); (* success label 2 *)
       L2_ast.TimesInstr(p,dest,L2_ast.IntTVal(p,4L));
       L2_ast.PlusInstr(p,dest,tv1);
       L2_ast.MemReadInstr(p,dest,dest,4L)]
   | AsetDExp(p,sv1,sv2,sv3) ->
      let sv1t = (compile_sval sv1) in
      let tv1 = L2_ast.get_tval sv1t in
      let sv2t = (compile_sval sv2) in
      let sv3t = (compile_sval sv3) in
      let tmp = L2_ast.Var(p,get_unique_varname prefix 0) in
      let tl1 = get_unique_varname prefix 1 in
      let tl2 = get_unique_varname prefix 2 in
      let fl = get_unique_varname prefix 3 in
      [L2_ast.AssignInstr(p,dest,sv2t);
       L2_ast.SrlInstr(p,dest,L2_ast.IntShVal(p,1L));
       L2_ast.MemReadInstr(p,tmp,L2_ast.get_var sv1t,0L);
       L2_ast.LtJumpInstr(p,L2_ast.VarTVal(p,dest),L2_ast.VarTVal(p,tmp),tl1,fl);
       L2_ast.LabelInstr(p,fl); (* fail label *)
       L2_ast.SllInstr(p,dest,L2_ast.IntShVal(p,1L));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1L));
       L2_ast.ArrayErrorInstr(p,tv1,L2_ast.VarTVal(p,dest));
       L2_ast.LabelInstr(p,tl1); (* success label 1 *)
       L2_ast.LtJumpInstr(p,L2_ast.VarTVal(p,dest),L2_ast.IntTVal(p,0L),fl,tl2);
       L2_ast.LabelInstr(p,tl2); (* success label 2 *)
       L2_ast.TimesInstr(p,dest,L2_ast.IntTVal(p,4L));
       L2_ast.PlusInstr(p,dest,tv1);
       L2_ast.MemWriteInstr(p,dest,4L,sv3t);
       L2_ast.AssignInstr(p,dest,L2_ast.IntSVal(p,1L))]
   | AlenDExp(p,sv) ->
      let v = L2_ast.get_var (compile_sval sv) in
      [L2_ast.MemReadInstr(p,dest,v,0L);
       L2_ast.SllInstr(p,dest,L2_ast.IntShVal(p,1L));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1L))]
   | PrintDExp(p,sv) ->
      let tv = L2_ast.get_tval (compile_sval sv) in
      [L2_ast.PrintInstr(p,tv);L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,L2_ast.EaxReg(p)))]
    (* (make-closure a b) is the same as (new-tuple a b)
     * (closure-proc a) is the same as (aref a 0)
     * (closure-vars a) is the same as (aref a 1) *)
   | MakeClosureDExp(p,s,sv) -> 
      compile_dexp (NewTupleDExp(p,[LabelSVal(p,s);sv])) dest tail prefix 
   | ClosureProcDExp(p,sv) -> 
      compile_dexp (ArefDExp(p,sv,IntSVal(p,0L))) dest tail prefix 
   | ClosureVarsDExp(p,sv) -> 
      compile_dexp (ArefDExp(p,sv,IntSVal(p,1L))) dest tail prefix 
   | SValDExp(p,sv) -> [L2_ast.AssignInstr(p,dest,compile_sval sv)]
and compile_sval (sv : L3_ast.sval) : L2_ast.sval =
   match sv with
   | VarSVal(p,v) -> L2_ast.VarSVal(p,compile_var v)
   (* here's where we do encoding of integer constants *)
   | IntSVal(p,i) -> L2_ast.IntSVal(p,(Int64.add (Int64.mul i 2L) 1L))
   | LabelSVal(p,l) -> L2_ast.LabelSVal(p,l)
and compile_var (v : L3_ast.var) : L2_ast.var = 
   match v with
   | Var(p,raw) ->
   (* L2 reserved words *)
   let resvd = ["esi";"edi";"ebp";"esp";"eax";"ecx";"edx";"ebx";
                "array-error";"tail-call";"allocate";"return";"cjump";"goto";"mem";"call"] in
   (* put the L3 prefix on reserved words *)
   let name = (try (concat_unique_names l3_prefix (List.find (fun x -> (x = raw)) resvd))
               with _ -> raw) in
   L2_ast.Var(p,name)
