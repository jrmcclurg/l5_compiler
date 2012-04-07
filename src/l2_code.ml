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
