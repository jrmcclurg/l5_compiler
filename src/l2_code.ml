(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/9/2012
 *
 * L2-to-L1 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l2_code.ml
 * In progress. Currently only has the "spill" function.
 *)

open L2_ast;;
open Utils;;


let compare_var (v1 : var) (v2 : var) : int =
  String.compare (get_var_name v1) (get_var_name v2)
;;

let rec list_contains (vl : var list) (v : var) =
   match vl with
   | [] -> false
   | t::ts ->
      if (compare_var t v) = 0 then true else list_contains ts v
;;


let sort_vars (vl : var list) : var list =
  List.sort compare_var vl
;;
      
(* TODO this is SLOW *)
let compute_ins (gens : var list) (kills : var list) (outs : var list) =
   let result = List.fold_right (fun o l ->
      if ((not (list_contains kills o)) && (not (list_contains l o))) then o::l else l
   ) outs gens in
   sort_vars result
;;

let rec compare_vars (vl1 : var list) (vl2 : var list) =
   match (vl1,vl2) with
   | ([],[]) -> true
   | ([],_) -> false
   | (_,[]) -> false
   | (a::ax,b::bx) -> ((compare_var a b) = 0) && (compare_vars ax bx)
;;

let print_var_list (vl : var list) =
  print_string "(";
      List.iter (fun v -> 
         print_var v;
         print_string ", "
      ) vl;
      print_string ")\n";
      ;;

let rec find_target_ins_helper (il : (instr * var list * var list) list) (s1 : string) (s2o : string option) : (var list) =
   match il with
   | [] -> []
   | (i,ins,_)::is ->
      let l = (match (i,s2o) with
      | (LabelInstr(_,s),None) -> (*print_string ("checking: "^s^"\n");*) if (s1 = s) then ins else []
      | (LabelInstr(_,s),Some(s2)) -> (*print_string ("checking: "^s^" with "^s1^", "^s2^"\n");*) if ((s1 = s) || (s2 = s)) then ins else []
      | _ -> []) in
      List.fold_right (fun i res -> 
         if (not (list_contains res i)) then i::res else res
      ) l (find_target_ins_helper is s1 s2o)

and find_target_ins (il : (instr * var list * var list) list) (s1 : string) (s2o : string option) : (var list) =
   let l = find_target_ins_helper il s1 s2o in
   sort_vars l
;;

let add_and_sort (vl : var list) (v : var) = 
   let r = if (not (list_contains vl v)) then v::vl else vl in
   sort_vars r
;;

(* given instruction i, returns (gens, kills) *)
let get_gens_kills (i : instr) : (var list * var list) =
   match i with
   | AssignInstr(_,v,VarSVal(_,v2)) -> ([v2], [v])
   | AssignInstr(_,v,_) -> ([], [v])
   | MemReadInstr(_,v1,v2,_) -> ([v2],[v1])
   | MemWriteInstr(_,v1,_,VarSVal(_,v2)) -> (add_and_sort [v1] v2,[])
   | MemWriteInstr(_,v1,_,_) -> ([v1],[])
   | PlusInstr(_,v,VarTVal(_,v2)) -> (add_and_sort [v] v2,[v])
   | PlusInstr(_,v,_) -> ([v], [v])
   | MinusInstr(_,v,VarTVal(_,v2)) -> (add_and_sort [v] v2,[v])
   | MinusInstr(_,v,_) -> ([v], [v])
   | TimesInstr(_,v,VarTVal(_,v2)) -> (add_and_sort [v] v2,[v])
   | TimesInstr(_,v,_) -> ([v], [v])
   | BitAndInstr(_,v,VarTVal(_,v2)) -> (add_and_sort [v] v2,[v])
   | BitAndInstr(_,v,_) -> ([v], [v])
   | SllInstr(_,v,ShVar(_,v2)) -> (add_and_sort [v] v2,[v])
   | SllInstr(_,v,_) -> ([v], [v])
   | SrlInstr(_,v,ShVar(_,v2)) -> (add_and_sort [v] v2,[v])
   | SrlInstr(_,v,_) -> ([v], [v])
   | LtInstr(_,v,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[v])
   | LtInstr(_,v,_,VarTVal(_,v3)) -> ([v3],[v])
   | LtInstr(_,v,VarTVal(_,v2),_) -> ([v2],[v])
   | LtInstr(_,v,_,_) -> ([], [v])
   | LeqInstr(_,v,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[v])
   | LeqInstr(_,v,_,VarTVal(_,v3)) -> ([v3],[v])
   | LeqInstr(_,v,VarTVal(_,v2),_) -> ([v2],[v])
   | LeqInstr(_,v,_,_) -> ([], [v])
   | EqInstr(_,v,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[v])
   | EqInstr(_,v,_,VarTVal(_,v3)) -> ([v3],[v])
   | EqInstr(_,v,VarTVal(_,v2),_) -> ([v2],[v])
   | EqInstr(_,v,_,_) -> ([], [v])
   | LabelInstr(_,_) -> ([],[])
   | GotoInstr(_,_) -> ([],[])
   | LtJumpInstr(_,VarTVal(_,v1),VarTVal(_,v2),_,_) -> (add_and_sort [v1] v2,[])
   | LtJumpInstr(_,_,VarTVal(_,v2),_,_) -> ([v2],[])
   | LtJumpInstr(_,VarTVal(_,v1),_,_,_) -> ([v1],[])
   | LeqJumpInstr(_,VarTVal(_,v1),VarTVal(_,v2),_,_) -> (add_and_sort [v1] v2,[])
   | LeqJumpInstr(_,_,VarTVal(_,v2),_,_) -> ([v2],[])
   | LeqJumpInstr(_,VarTVal(_,v1),_,_,_) -> ([v1],[])
   | EqJumpInstr(_,VarTVal(_,v1),VarTVal(_,v2),_,_) -> (add_and_sort [v1] v2,[])
   | EqJumpInstr(_,_,VarTVal(_,v2),_,_) -> ([v2],[])
   | EqJumpInstr(_,VarTVal(_,v1),_,_,_) -> ([v1],[])
   | CallInstr(_,VarUVal(p,v)) ->
      let l = add_and_sort [EaxReg(p);EdxReg(p);EcxReg(p)] v in
      (l,[EaxReg(p);EbxReg(p);EcxReg(p);EdxReg(p)])
   | CallInstr(p,_) -> ([EaxReg(p);EcxReg(p);EdxReg(p)],[EaxReg(p);EbxReg(p);EcxReg(p);EdxReg(p)])
   | TailCallInstr(_,VarUVal(p,v)) -> (* TODO XXX - something is wrong here! *)
      let l = add_and_sort [EaxReg(p);EdxReg(p);EcxReg(p);EdiReg(p);EsiReg(p)] v in
      (l,[])
   | TailCallInstr(p,_) -> ([EaxReg(p);EcxReg(p);EdiReg(p);EdxReg(p);EsiReg(p)],[])
   | ReturnInstr(p) -> ([EaxReg(p);EdiReg(p);EsiReg(p)],[])
   | PrintInstr(p,VarTVal(_,v)) -> ([v],[EaxReg(p)])
   | PrintInstr(p,_) -> ([],[EaxReg(p)])
   | AllocInstr(p,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[EaxReg(p)])
   | AllocInstr(p,_,VarTVal(_,v3)) -> ([v3],[EaxReg(p)])
   | AllocInstr(p,VarTVal(_,v2),_) -> ([v2],[EaxReg(p)])
   | ArrayErrorInstr(p,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[EaxReg(p)]) (* TODO XXX - something wrong *)
   | ArrayErrorInstr(p,_,VarTVal(_,v3)) -> ([v3],[EaxReg(p)])
   | ArrayErrorInstr(p,VarTVal(_,v2),_) -> ([v2],[EaxReg(p)])
   | _ -> ([],[])
;;

let rec liveness_helper (il : (instr * var list * var list) list) : ((instr * var list * var list) list) =
   let (_,result,change) = List.fold_right (fun (i,ins,outs) (prev_ins,res,flag) -> 
      let (gens,kills) = get_gens_kills i in
      let new_ins = compute_ins gens kills outs in
      let new_outs = (match i with
      | GotoInstr(_,s) -> find_target_ins il s None
      | LtJumpInstr(_,_,_,s1,s2) -> find_target_ins il s1 (Some(s2))
      | LeqJumpInstr(_,_,_,s1,s2) -> find_target_ins il s1 (Some(s2))
      | EqJumpInstr(_,_,_,s1,s2) -> find_target_ins il s1 (Some(s2))
      | _ -> prev_ins) in
      (*print_string "Comparing:\n";
      print_var_list ins;
      print_var_list new_ins;
      print_string "Also:\n";
      print_var_list outs;
      print_var_list new_outs;*)
      (ins,(i,new_ins,new_outs)::res,flag || (not (compare_vars ins new_ins)) || (not (compare_vars outs new_outs)))
   ) il ([],[],false) in
   if change then liveness_helper result else result
;;

let liveness (il : instr list) : ((var list) list * (var list) list) = 
   let nl = List.map (fun i -> (i,[],[])) il in
   let l = liveness_helper nl in
   List.fold_right (fun (i,ins,outs) (inl,outl) -> (ins::inl,outs::outl)) l ([],[])
;;

let rec spill (il : instr list) (v : string) (off : int64) (prefix : string) : instr list =
   (* go through the list of instructions... *)
   let (result,_) = List.fold_left (fun (l,k) i -> (* l is the cumulative list, k is the unique number,
                                                    * and i is the current instruction to process *)
      let p = get_pos_instr i in (* the the Pos of the instruction *)
      let new_prefix = (prefix^(string_of_int k)) in (* compute a unique variable name *)
      let header = MemReadInstr(p,Var(p,new_prefix),EbpReg(p),off) in (* a 'header' instruction (i.e. one that
                                                                       * does (unique_var <- (mem ebp offset)) *)
      let footer = MemWriteInstr(p,EbpReg(p),off,
                                   VarSVal(p,Var(p,new_prefix))) in (* a 'footer' instruction (i.e.
                                                                     * one that does
                                                                     * ((mem ebp offset) <- unique_var)) *)
      (* check to see what instruction we have *)
      match i with
      (* (v1 <- sv) *)
      | AssignInstr(p1,v1,sv) ->
         (* if v1 is equal to the spill variable, the new instruction (i1) will be ((mem ebp offset) <- sv) *)
         let (write,i1,s1) = (match v1 with
            | Var(p2,s) -> if (s = v) then
               (true,MemWriteInstr(p2,EbpReg(p2),off,sv),Some(s)) else (false,i,None)
            | _ -> (false,i,None)) in
         (* if sv is equal to the spill variable, the new instruction (i2) will be (v1 <- (mem ebp offset)) *)
         let (read,i2,s2) = (match sv with
            | VarSVal(p2,Var(p3,s)) ->
               if (s = v) then
                  (true,MemReadInstr(p3,v1,EbpReg(p3),off),Some(s)) else (false,i,None)
            | _ -> (false,i,None)) in
         (* if v1,sv are both equal to the spill variable, we will drop this instruction *)
         let drop = (match (s1,s2) with
            | (Some(ss1),Some(ss2)) -> (ss1 = ss2)
            | _ -> false) in
         let new_inst = if write then i1 else i2 in
         (* if we generated a new instruction (i.e. (read || write) is true), use it.
          * otherwise, just use the current instruction i without modification *)
         let l1 = if drop then [] else if (read || write) then [new_inst] else [i] in
         (* notice that a unique variable name is never used for this instruction, so k stays the same. *)
         (* also, notice that the header/footer instructions are not used *)
         (l@l1,k)
      (* (v1 <- (mem v2 i)) *)
      | MemReadInstr(p1,v1,v2,i) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v3) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if v2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,v4) = (match v2 with
            | Var(p2,s) ->
               if (s = v) then (true,Var(p2,new_prefix)) else (false,v2)
            | _ -> (false,v2)) in
         (* the new instruction is the same, with v1 and/or v2 possibly replaced by a unique var name *)
         let new_inst = MemReadInstr(p1,v3,v4,i) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if read is true (i.e. if this instruction reads from the unique variable,
          * it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if read then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* ((mem v1 i) <- v2) *)
      | MemWriteInstr(p1,v1,i,sv) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if sv2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,sv2) = (match sv with
            | VarSVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarSVal(p2,Var(p3,new_prefix))) else (false,sv)
            | _ -> (false,sv)) in
         (* the new instruction is the same, with v1 and/or sv2 possibly replaced by a unique var name *)
         let new_inst = MemWriteInstr(p1,v2,i,sv2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1 || read2) then k+1 else k in
         (* we don't ever need the footer instruction here, because no variable gets written to *)
         (* prepend the header instruction if (read1 || read2) is true (i.e. if this instruction reads
          * from the unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = new_inst::l1 in
         let l3 = if (read1 || read2) then header::l2 else l2 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l3,new_k)
      (* (v1 += t) *)
      | PlusInstr(p1,v1,t) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,t2) = (match t with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t)
            | _ -> (false,t)) in
         (* the new instruction is the same, with v1 and/or t possibly replaced by a unique var name *)
         let new_inst = PlusInstr(p1,v2,t2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if (read || write) is true (i.e. if this instruction reads from
          * the unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read || write) then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* (v1 -= t) *)
      | MinusInstr(p1,v1,t) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,t2) = (match t with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t)
            | _ -> (false,t)) in
         (* the new instruction is the same, with v1 and/or t possibly replaced by a unique var name *)
         let new_inst = MinusInstr(p1,v2,t2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if (read || write) is true (i.e. if this instruction reads from
          * the unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read || write) then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* (v1 *= t) *)
      | TimesInstr(p1,v1,t) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,t2) = (match t with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t)
            | _ -> (false,t)) in
         (* the new instruction is the same, with v1 and/or t possibly replaced by a unique var name *)
         let new_inst = TimesInstr(p1,v2,t2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if (read || write) is true (i.e. if this instruction reads from
          * the unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read || write) then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* (v1 &= t) *)
      | BitAndInstr(p1,v1,t) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,t2) = (match t with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t)
            | _ -> (false,t)) in
         (* the new instruction is the same, with v1 and/or t possibly replaced by a unique var name *)
         let new_inst = BitAndInstr(p1,v2,t2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if (read || write) is true (i.e. if this instruction reads from
          * the unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read || write) then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* (v1 <<= svr) *)
      | SllInstr(p1,v1,svr) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if svr is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,svr2) = (match svr with
            | ShVar(p2,Var(p3,s)) ->
               if (s = v) then (true,ShVar(p2,Var(p3,new_prefix))) else (false,svr)
            | _ -> (false,svr)) in
         (* the new instruction is the same, with v1 and/or svr possibly replaced by a unique var name *)
         let new_inst = SllInstr(p1,v2,svr2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if (read || write) is true (i.e. if this instruction reads from
          * the unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read || write) then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* (v1 >>= svr) *)
      | SrlInstr(p1,v1,svr) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if svr is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,svr2) = (match svr with
            | ShVar(p2,Var(p3,s)) ->
               if (s = v) then (true,ShVar(p2,Var(p3,new_prefix))) else (false,svr)
            | _ -> (false,svr)) in
         (* the new instruction is the same, with v1 and/or svr possibly replaced by a unique var name *)
         let new_inst = SrlInstr(p1,v2,svr2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if (read || write) is true (i.e. if this instruction reads from
          * the unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read || write) then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* (v1 <- t1 < t2) *)
      | LtInstr(p1,v1,t1,t2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         (* the new instruction is the same, with v1 and/or t1 and/or t2 possibly replaced by a unique var name *)
         let new_inst = LtInstr(p1,v2,t3,t4) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1 || read2 || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if (read1 || read2) is true (i.e. if this instruction reads from the
          * unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read1 || read2) then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* (v1 <- t1 <= t2) *)
      | LeqInstr(p1,v1,t1,t2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         (* the new instruction is the same, with v1 and/or t1 and/or t2 possibly replaced by a unique var name *)
         let new_inst = LeqInstr(p1,v2,t3,t4) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1 || read2 || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if (read1 || read2) is true (i.e. if this instruction reads from the
          * unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read1 || read2) then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* (v1 <- t1 = t2) *)
      | EqInstr(p1,v1,t1,t2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         (* the new instruction is the same, with v1 and/or t1 and/or t2 possibly replaced by a unique var name *)
         let new_inst = EqInstr(p1,v2,t3,t4) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1 || read2 || write) then k+1 else k in
         (* append the footer instruction if write is true (i.e. if this instruction writes to the unique variable,
          * it must be subsequently written back to memory) *)
         (* prepend the header instruction if (read1 || read2) is true (i.e. if this instruction reads from the
          * unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read1 || read2) then header::l3 else l3 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l4,new_k)
      (* (cjump t1 < t2 s1 s2) *)
      | LtJumpInstr(p1,t1,t2,s1,s2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         (* the new instruction is the same, with t1 and/or t2 possibly replaced by a unique var name *)
         let new_inst = LtJumpInstr(p1,t3,t4,s1,s2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1 || read2) then k+1 else k in
         (* this instruction never writes a variable, so we don't use the header instruction *)
         (* prepend the header instruction if (read1 || read2) is true (i.e. if this instruction reads from the
          * unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = new_inst::l1 in
         let l3 = if (read1 || read2) then header::l2 else l2 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l3,new_k)
      (* (cjump t1 <= t2 s1 s2) *)
      | LeqJumpInstr(p1,t1,t2,s1,s2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         (* the new instruction is the same, with t1 and/or t2 possibly replaced by a unique var name *)
         let new_inst = LeqJumpInstr(p1,t3,t4,s1,s2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1 || read2) then k+1 else k in
         (* this instruction never writes a variable, so we don't use the header instruction *)
         (* prepend the header instruction if (read1 || read2) is true (i.e. if this instruction reads from the
          * unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = new_inst::l1 in
         let l3 = if (read1 || read2) then header::l2 else l2 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l3,new_k)
      (* (cjump t1 = t2 s1 s2) *)
      | EqJumpInstr(p1,t1,t2,s1,s2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         (* the new instruction is the same, with t1 and/or t2 possibly replaced by a unique var name *)
         let new_inst = EqJumpInstr(p1,t3,t4,s1,s2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1 || read2) then k+1 else k in
         (* this instruction never writes a variable, so we don't use the header instruction *)
         (* prepend the header instruction if (read1 || read2) is true (i.e. if this instruction reads from the
          * unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = new_inst::l1 in
         let l3 = if (read1 || read2) then header::l2 else l2 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l3,new_k)
      (* (call u) *)
      | CallInstr(p1,u) ->
         (* if u is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,u2) = (match u with
            | VarUVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarUVal(p2,Var(p3,new_prefix))) else (false,u)
            | _ -> (false,u)) in
         (* the new instruction is the same, with u possibly replaced by a unique var name *)
         let new_inst = CallInstr(p1,u2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1) then k+1 else k in
         (* this instruction never writes a variable, so we don't use the header instruction *)
         (* prepend the header instruction if (read1) is true (i.e. if this instruction reads from the
          * unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = new_inst::l1 in
         let l3 = if (read1) then header::l2 else l2 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l3,new_k)
      (* (tail-call u) *)
      | TailCallInstr(p1,u) ->
         (* if u is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,u2) = (match u with
            | VarUVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarUVal(p2,Var(p3,new_prefix))) else (false,u)
            | _ -> (false,u)) in
         (* the new instruction is the same, with u possibly replaced by a unique var name *)
         let new_inst = TailCallInstr(p1,u2) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1) then k+1 else k in
         (* this instruction never writes a variable, so we don't use the header instruction *)
         (* prepend the header instruction if (read1) is true (i.e. if this instruction reads from the
          * unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = new_inst::l1 in
         let l3 = if (read1) then header::l2 else l2 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l3,new_k)
      (* (eax <- (print t1)) *)
      | PrintInstr(p1,t1) ->
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         (* the new instruction is the same, with t1 possibly replaced by a unique var name *)
         let new_inst = PrintInstr(p1,t3) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1) then k+1 else k in
         (* this instruction never writes a variable, so we don't use the header instruction *)
         (* prepend the header instruction if (read1) is true (i.e. if this instruction reads from the
          * unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = new_inst::l1 in
         let l3 = if (read1) then header::l2 else l2 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l3,new_k)
      (* (eax <- (allocate t1 t2)) *)
      | AllocInstr(p1,t1,t2) ->
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         (* the new instruction is the same, with t1 and/or t2 possibly replaced by a unique var name *)
         let new_inst = AllocInstr(p1,t3,t4) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1 || read2) then k+1 else k in
         (* this instruction never writes a variable, so we don't use the header instruction *)
         (* prepend the header instruction if (read1 || read2) is true (i.e. if this instruction
          * reads from the unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = new_inst::l1 in
         let l3 = if (read1 || read2) then header::l2 else l2 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l3,new_k)
      (* (eax <- (array-error t1 t2)) *)
      | ArrayErrorInstr(p1,t1,t2) ->
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         (* the new instruction is the same, with t1 and/or t2 possibly replaced by a unique var name *)
         let new_inst = ArrayErrorInstr(p1,t3,t4) in
         (* if we used a unique var name, increment the counter *)
         let new_k = if (read1 || read2) then k+1 else k in
         (* this instruction never writes a variable, so we don't use the header instruction *)
         (* prepend the header instruction if (read1 || read2) is true (i.e. if this instruction
          * reads from the unique variable, it must first be read from memory) *)
         let l1 = [] in
         let l2 = new_inst::l1 in
         let l3 = if (read1 || read2) then header::l2 else l2 in
         (* add our instruction(s) to the list, and inform the loop of the new unique number *)
         (l@l3,new_k)
      | _ -> (l@[i],k)
   ) ([],0) il in result (* start with an empty list and unique counter "0". return the expanded
                          * list of instructions *)
;;
