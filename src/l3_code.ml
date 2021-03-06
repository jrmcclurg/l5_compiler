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
open Flags;;

let resvd_words = [
   add_symbol "esi";
   add_symbol "edi";
   add_symbol "ebp";
   add_symbol "esp";
   add_symbol "eax";
   add_symbol "ecx";
   add_symbol "edx";
   add_symbol "ebx";
   add_symbol "array-error";
   add_symbol "tail-call";
   add_symbol "allocate";
   add_symbol "return";
   add_symbol "cjump";
   add_symbol "goto";
   add_symbol "mem";
   add_symbol "call"
];;

(*********************************************************
 **  L3-to-L2 CODE GENERATION                           **
 *********************************************************)

(* compile an L2 program into an L1 program *)

let rec compile_program (p : L3_ast.program) : L2_ast.program =
   match p with
   | Program(p,e,fl) -> 
      let start_time = Sys.time () in
      if !debug_3 || !verbose_mode then (
         print_string ("Compiling L3 to L2..."^(if !verbose_mode then " " else "\n"));
         flush Pervasives.stdout
      );
      (* compile all the functions into L1 functions, giving
       * each one a unique count (starting with 0) *)
      let (_,fl2) = List.fold_left (fun (count,res) f ->
         (count+1,res@[compile_func f])
      ) (1,[]) fl in (* start with the unique id "1", since we use "0" for
                      * the exp "e" *)
      let main = (L2_ast.Function(p,None,compile_exp e true)) in
      if !debug_3 || !verbose_mode then (
         let diff = (Sys.time ()) -. start_time in
         print_string ((if !verbose_mode then "" else "...")^"done"^
            (if !verbose_mode then "" else " with L3->L2")^": "^(string_of_float diff)^" sec.\n");
         flush Pervasives.stdout
      );
      L2_ast.Program(p, main::fl2)
and compile_func (f : L3_ast.func) : L2_ast.func = 
   match f with
   | Function(p,name,vl,e) ->
      let regs = [L2_ast.ecx_id;L2_ast.edx_id;L2_ast.eax_id] in
      if ((List.length vl) > 3) then die_error p "more than 3 function args";
      let (_,il1) = List.fold_left (fun (k,res) v ->
         let reg = List.nth regs k in
         let i = L2_ast.AssignInstr(p,compile_var v,L2_ast.VarSVal(p,L2_ast.VarOrReg(p,reg,false))) in
         (k+1, res@[i])
      ) (0,[]) vl in
      let il2 = compile_exp e false in
      L2_ast.Function(p, Some(name), il1@il2)
and compile_exp (e : L3_ast.exp) (first : bool) : L2_ast.instr list = 
   match e with
   | LetExp(p,v,de,e) ->
      (* generate the L2 variable *)
      let v2 = compile_var v in
      (* compile the "d" and store the result in the compiled var *)
      (compile_dexp de v2 false)@
      (* compile the "e" *)
      (compile_exp e first)
   | IfExp(p,sv,e1,e2) ->
      let tv = L2_ast.get_tval (compile_sval sv) in
      let il1 = (compile_exp e1 first) in
      let il2 = (compile_exp e2 first) in
      let tl = get_unique_symbol l3_prefix (*prefix 2*) in
      let fl = get_unique_symbol l3_prefix (*prefix 3*) in
      let jl = get_unique_symbol l3_prefix (*prefix 4*) in
      let i = L2_ast.EqJumpInstr(p,tv,L2_ast.IntTVal(p,1l),fl,tl) in
      i::(L2_ast.LabelInstr(p,tl))::il1@
      [L2_ast.GotoInstr(p,jl);L2_ast.LabelInstr(p,fl)]
      @il2@[L2_ast.LabelInstr(p,jl);
      (* we put the (eax <- eax) instruction at the end, because the L2
       * interpreter complains about functions ending with a label *)
      L2_ast.AssignInstr(p,L2_ast.VarOrReg(p,L2_ast.eax_id,false),L2_ast.VarSVal(p,L2_ast.VarOrReg(p,L2_ast.eax_id,false)))]
   | DExpExp(p,de) -> 
      let tail = (not first) in
      (compile_dexp de (L2_ast.VarOrReg(p,L2_ast.eax_id,false)) tail)@
      (if first then [] else [L2_ast.ReturnInstr(p)]) (* only add (return) instr in main function *)
and compile_dexp (de : L3_ast.dexp) (dest : L2_ast.var) (tail : bool) : L2_ast.instr list = 
   match de with
   | PlusDExp(p,sv1,sv2) ->
      (* (2a+1)+(2b+1)-1 = 2a+1+2b+1-1 = 2a+2b+1 = 2(a+b)+1  *)
      let tmpd = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 0*)) in
      let sv1t = compile_sval sv1 in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.AssignInstr(p,tmpd,sv1t);
       L2_ast.PlusInstr(p,tmpd,tv2);
       L2_ast.MinusInstr(p,tmpd,L2_ast.IntTVal(p,1l));
       L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,tmpd))]
   | MinusDExp(p,sv1,sv2) ->
      (* (2a+1)-(2b+1)+1 = 2a+1-2b-1+1 = 2a-2b+1 = 2(a-b)+1  *)
      let tmpd = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 0*)) in
      let sv1t = compile_sval sv1 in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.AssignInstr(p,tmpd,sv1t);
       L2_ast.MinusInstr(p,tmpd,tv2);
       L2_ast.PlusInstr(p,tmpd,L2_ast.IntTVal(p,1l));
       L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,tmpd))]
   | TimesDExp(p,sv1,sv2) ->
      (* just decode both, multiply, and then encode *)
      let tmp = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 0*)) in
      let sv1t = compile_sval sv1 in
      let sv2t = compile_sval sv2 in
      [L2_ast.AssignInstr(p,tmp,sv1t);
       L2_ast.SrlInstr(p,tmp,L2_ast.IntShVal(p,1l));
       L2_ast.AssignInstr(p,dest,sv2t);
       L2_ast.SrlInstr(p,dest,L2_ast.IntShVal(p,1l));
       L2_ast.TimesInstr(p,dest,L2_ast.VarTVal(p,tmp));
       L2_ast.TimesInstr(p,dest,L2_ast.IntTVal(p,2l));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1l))]@
       (if !clear_uninit then [L2_ast.AssignInstr(p,tmp,L2_ast.IntSVal(p,1l))] else [])
   | LtDExp(p,sv1,sv2) ->
      let tmpd = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 0*)) in
      let tv1 = L2_ast.get_tval (compile_sval sv1) in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.LtInstr(p,tmpd,tv1,tv2);
       L2_ast.SllInstr(p,tmpd,L2_ast.IntShVal(p,1l));
       L2_ast.PlusInstr(p,tmpd,L2_ast.IntTVal(p,1l));
       L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,tmpd))]
   | LeqDExp(p,sv1,sv2) ->
      let tmpd = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 0*)) in
      let tv1 = L2_ast.get_tval (compile_sval sv1) in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.LeqInstr(p,tmpd,tv1,tv2);
       L2_ast.SllInstr(p,tmpd,L2_ast.IntShVal(p,1l));
       L2_ast.PlusInstr(p,tmpd,L2_ast.IntTVal(p,1l));
       L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,tmpd))]
   | EqDExp(p,sv1,sv2) ->
      let tmpd = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 0*)) in
      let tv1 = L2_ast.get_tval (compile_sval sv1) in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.EqInstr(p,tmpd,tv1,tv2);
       L2_ast.SllInstr(p,tmpd,L2_ast.IntShVal(p,1l));
       L2_ast.PlusInstr(p,tmpd,L2_ast.IntTVal(p,1l));
       L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,tmpd))]
   | NumberPredDExp(p,sv) ->
      let sv1t = compile_sval sv in
      [L2_ast.AssignInstr(p,dest,sv1t);
       L2_ast.BitAndInstr(p,dest,L2_ast.IntTVal(p,1l));
       L2_ast.SllInstr(p,dest,L2_ast.IntShVal(p,1l));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1l))]
   | ArrayPredDExp(p,sv) ->
      let sv1t = compile_sval sv in
      [L2_ast.AssignInstr(p,dest,sv1t);
       L2_ast.BitAndInstr(p,dest,L2_ast.IntTVal(p,1l));
       L2_ast.TimesInstr(p,dest,L2_ast.IntTVal(p,-2l));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,3l))]
   | AppDExp(p,sv,svl) ->
      let regs = [L2_ast.ecx_id;L2_ast.edx_id;L2_ast.eax_id] in
      if ((List.length svl) > 3) then die_error p "more than 3 function args";
      let (_,il1) = List.fold_left (fun (k,res) v ->
         let reg = List.nth regs k in
         let i = L2_ast.AssignInstr(p,L2_ast.VarOrReg(p,reg,false),compile_sval v) in
         (k+1, res@[i])
      ) (0,[]) svl in
      let uv = L2_ast.get_uval (compile_sval sv) in
      il1@(if tail then [L2_ast.TailCallInstr(p,uv)] else [L2_ast.CallInstr(p,uv)])@
      [L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,L2_ast.VarOrReg(p,L2_ast.eax_id,false)))]
   | NewArrayDExp(p,sv1,sv2) ->
      let tv1 = L2_ast.get_tval (compile_sval sv1) in
      let tv2 = L2_ast.get_tval (compile_sval sv2) in
      [L2_ast.AllocInstr(p,tv1,tv2);
       L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,L2_ast.VarOrReg(p,L2_ast.eax_id,false)))]
   | NewTupleDExp(p,svl) ->
      let len = List.length svl in
      let uv = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true) in
      let has_dexp = dexp_list_is_flat svl in
      let the_src = (if has_dexp then L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true)
                                 else L2_ast.VarOrReg(p,L2_ast.eax_id,false)) in
      let (_,l2) = List.fold_left (fun (off,res) sv ->
         let (pre_list,comp_sv) = (match sv with
         | SValDExp(p,sv) -> ([],compile_sval sv)
         | _ -> 
            (compile_dexp sv uv false, L2_ast.VarSVal(p,uv))
         ) in
         ((off+4),res@pre_list@
         [L2_ast.MemWriteInstr(p,the_src,Int32.of_int off,comp_sv)])
      ) (4,[]) svl in
      [L2_ast.AllocInstr(p,L2_ast.IntTVal(p,Int32.of_int (2*len+1)),L2_ast.IntTVal(p,0l))]@
      (if has_dexp then [L2_ast.AssignInstr(p,the_src,L2_ast.VarSVal(p,L2_ast.VarOrReg(p,L2_ast.eax_id,false)))] else [])@l2@
      [L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,the_src))]
   | ArefDExp(p,sv1,sv2) ->
      let sv1t = (compile_sval sv1) in
      let tv1 = L2_ast.get_tval sv1t in
      let sv2t = (compile_sval sv2) in
      let tmpd = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 0*)) in
      let tmp = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 1*)) in
      let tl1 = get_unique_symbol l3_prefix (*prefix 1*) in
      let tl2 = get_unique_symbol l3_prefix (*prefix 2*) in
      let fl = get_unique_symbol l3_prefix (*prefix 3*) in
      [L2_ast.AssignInstr(p,tmpd,sv2t);
       L2_ast.SrlInstr(p,tmpd,L2_ast.IntShVal(p,1l));
       L2_ast.MemReadInstr(p,tmp,L2_ast.get_var sv1t,0l);
       L2_ast.LtJumpInstr(p,L2_ast.VarTVal(p,tmpd),L2_ast.VarTVal(p,tmp),tl1,fl);
       L2_ast.LabelInstr(p,fl); (* fail label *)
       L2_ast.SllInstr(p,tmpd,L2_ast.IntShVal(p,1l));
       L2_ast.PlusInstr(p,tmpd,L2_ast.IntTVal(p,1l));
       L2_ast.ArrayErrorInstr(p,tv1,L2_ast.VarTVal(p,tmpd));
       L2_ast.LabelInstr(p,tl1); (* success label 1 *)
       L2_ast.LtJumpInstr(p,L2_ast.VarTVal(p,tmpd),L2_ast.IntTVal(p,0l),fl,tl2);
       L2_ast.LabelInstr(p,tl2); (* success label 2 *)
       L2_ast.TimesInstr(p,tmpd,L2_ast.IntTVal(p,4l));
       L2_ast.PlusInstr(p,tmpd,tv1);
       L2_ast.MemReadInstr(p,dest,tmpd,4l)]@
       (if !clear_uninit then [L2_ast.AssignInstr(p,tmpd,L2_ast.IntSVal(p,1l));
       L2_ast.AssignInstr(p,tmp,L2_ast.IntSVal(p,1l))] else [])
   | AsetDExp(p,sv1,sv2,sv3) ->
      let sv1t = (compile_sval sv1) in
      let tv1 = L2_ast.get_tval sv1t in
      let sv2t = (compile_sval sv2) in
      let sv3t = (compile_sval sv3) in
      let tmpd = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 0*)) in
      let tmp = L2_ast.VarOrReg(p,get_unique_symbol l3_prefix,true (*prefix 1*)) in
      let tl1 = get_unique_symbol l3_prefix (*prefix 2*) in
      let tl2 = get_unique_symbol l3_prefix (*prefix 3*) in
      let fl = get_unique_symbol l3_prefix (*prefix n4*) in
      [L2_ast.AssignInstr(p,tmpd,sv2t);
       L2_ast.SrlInstr(p,tmpd,L2_ast.IntShVal(p,1l));
       L2_ast.MemReadInstr(p,tmp,L2_ast.get_var sv1t,0l);
       L2_ast.LtJumpInstr(p,L2_ast.VarTVal(p,tmpd),L2_ast.VarTVal(p,tmp),tl1,fl);
       L2_ast.LabelInstr(p,fl); (* fail label *)
       L2_ast.SllInstr(p,tmpd,L2_ast.IntShVal(p,1l));
       L2_ast.PlusInstr(p,tmpd,L2_ast.IntTVal(p,1l));
       L2_ast.ArrayErrorInstr(p,tv1,L2_ast.VarTVal(p,tmpd));
       L2_ast.LabelInstr(p,tl1); (* success label 1 *)
       L2_ast.LtJumpInstr(p,L2_ast.VarTVal(p,tmpd),L2_ast.IntTVal(p,0l),fl,tl2);
       L2_ast.LabelInstr(p,tl2); (* success label 2 *)
       L2_ast.TimesInstr(p,tmpd,L2_ast.IntTVal(p,4l));
       L2_ast.PlusInstr(p,tmpd,tv1);
       L2_ast.MemWriteInstr(p,tmpd,4l,sv3t);
       L2_ast.AssignInstr(p,dest,L2_ast.IntSVal(p,1l))]@
       (if !clear_uninit then [L2_ast.AssignInstr(p,tmp,L2_ast.IntSVal(p,1l));
                               L2_ast.AssignInstr(p,tmpd,L2_ast.IntSVal(p,1l))] else [])
   | AlenDExp(p,sv) ->
      let v = L2_ast.get_var (compile_sval sv) in
      [L2_ast.MemReadInstr(p,dest,v,0l);
       L2_ast.SllInstr(p,dest,L2_ast.IntShVal(p,1l));
       L2_ast.PlusInstr(p,dest,L2_ast.IntTVal(p,1l))]
   | PrintDExp(p,sv) ->
      let tv = L2_ast.get_tval (compile_sval sv) in
      [L2_ast.PrintInstr(p,tv);L2_ast.AssignInstr(p,dest,L2_ast.VarSVal(p,L2_ast.VarOrReg(p,L2_ast.eax_id,false)))]
    (* (make-closure a b) is the same as (new-tuple a b)
     * (closure-proc a) is the same as (aref a 0)
     * (closure-vars a) is the same as (aref a 1) *)
   | MakeClosureDExp(p,s,sv) -> 
      compile_dexp (NewTupleDExp(p,[SValDExp(p,LabelSVal(p,s));SValDExp(p,sv)])) dest tail 
   | ClosureProcDExp(p,sv) -> 
      compile_dexp (ArefDExp(p,sv,IntSVal(p,0l))) dest tail
   | ClosureVarsDExp(p,sv) -> 
      compile_dexp (ArefDExp(p,sv,IntSVal(p,1l))) dest tail
   | SValDExp(p,sv) -> [L2_ast.AssignInstr(p,dest,compile_sval sv)]
and compile_sval (sv : L3_ast.sval) : L2_ast.sval =
   match sv with
   | VarSVal(p,v) -> L2_ast.VarSVal(p,compile_var v)
   (* here's where we do encoding of integer constants *)
   | IntSVal(p,i) -> L2_ast.IntSVal(p,(Int32.add (Int32.mul i 2l) 1l))
   | LabelSVal(p,l) -> L2_ast.LabelSVal(p,l)
and compile_var (v : L3_ast.var) : L2_ast.var = 
   match v with
   | Var(p,raw) ->
   (* L2 reserved words *)
   (* put the L3 prefix on reserved words *)
   let id = (try add_symbol (make_ident_unique l3_prefix (get_symbol (List.find (fun x -> (x = raw)) resvd_words))) (* TODO - these unique var names look ugly *)
               with _ -> raw) in
   L2_ast.VarOrReg(p,id,true)
;;
