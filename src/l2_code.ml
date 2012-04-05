(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/3/2012
 *
 * L2-to-L1 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l2_code.ml
 * In progress
 *)

open L2_ast;;
open Utils;;

let rec spill (il : instr list) (v : string) (off : int64) (prefix : string) : instr list =
   (* pull variables out of assignments and the RHS of other instructions *)
   let (result,_) = List.fold_left (fun (l,k) i ->
      let p = get_pos_instr i in
      let new_prefix = (prefix^(string_of_int k)) in
      let header = MemReadInstr(p,Var(p,new_prefix),EbpReg(p),off) in
      let footer = MemWriteInstr(p,EbpReg(p),off,VarSVal(p,Var(p,new_prefix))) in
      match i with
      | AssignInstr(_,Var(_,s1),VarSVal(_,Var(_,s2))) ->
         if ((s1 = v) && (s2 = v)) then
            (l,k)
         else (l@[i],k)
      | AssignInstr(p1,Var(p2,s),sv) ->
         if (s = v) then
            (l@[MemWriteInstr(p1,EbpReg(p2),off,sv)],k)
         else (l@[i],k)
      | AssignInstr(p1,v1,VarSVal(p2,Var(p3,s))) ->
         if (s = v) then
            (l@[MemReadInstr(p1,v1,EbpReg(p2),off)],k)
         else (l@[i],k)
      | MemReadInstr(p1,v1,v2,i) ->
         let (write,v3) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read,v4) = (match v2 with
            | Var(p2,s) ->
               if (s = v) then (true,Var(p2,new_prefix)) else (false,v2)
            | _ -> (false,v2)) in
         let new_inst = MemReadInstr(p1,v3,v4,i) in
         let new_k = if (read || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if read then header::l3 else l3 in
         (l@l4,new_k)
      | MemWriteInstr(p1,v1,i,sv) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read,sv2) = (match sv with
            | VarSVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarSVal(p2,Var(p3,new_prefix))) else (false,sv)
            | _ -> (false,sv)) in
         let new_inst = MemWriteInstr(p1,v2,i,sv2) in
         let new_k = if (read || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if read then header::l3 else l3 in
         (l@l4,new_k)
      | PlusInstr(p1,v1,t) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read,t2) = (match t with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t)
            | _ -> (false,t)) in
         let new_inst = PlusInstr(p1,v2,t2) in
         let new_k = if (read || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if read then header::l3 else l3 in
         (l@l4,new_k)
      | MinusInstr(p1,v1,t) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read,t2) = (match t with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t)
            | _ -> (false,t)) in
         let new_inst = MinusInstr(p1,v2,t2) in
         let new_k = if (read || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if read then header::l3 else l3 in
         (l@l4,new_k)
      | TimesInstr(p1,v1,t) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read,t2) = (match t with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t)
            | _ -> (false,t)) in
         let new_inst = TimesInstr(p1,v2,t2) in
         let new_k = if (read || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if read then header::l3 else l3 in
         (l@l4,new_k)
      | BitAndInstr(p1,v1,t) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read,t2) = (match t with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t)
            | _ -> (false,t)) in
         let new_inst = BitAndInstr(p1,v2,t2) in
         let new_k = if (read || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if read then header::l3 else l3 in
         (l@l4,new_k)
      | LtInstr(p1,v1,t1,t2) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         let new_inst = LtInstr(p1,v2,t3,t4) in
         let new_k = if (read1 || read2 || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read1 || read2) then header::l3 else l3 in
         (l@l4,new_k)
      | LeqInstr(p1,v1,t1,t2) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         let new_inst = LeqInstr(p1,v2,t3,t4) in
         let new_k = if (read1 || read2 || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read1 || read2) then header::l3 else l3 in
         (l@l4,new_k)
      | EqInstr(p1,v1,t1,t2) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read1,t3) = (match t1 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t1)
            | _ -> (false,t1)) in
         let (read2,t4) = (match t2 with
            | VarTVal(p2,Var(p3,s)) ->
               if (s = v) then (true,VarTVal(p2,Var(p3,new_prefix))) else (false,t2)
            | _ -> (false,t2)) in
         let new_inst = EqInstr(p1,v2,t3,t4) in
         let new_k = if (read1 || read2 || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if (read1 || read2) then header::l3 else l3 in
         (l@l4,new_k)
      | SllInstr(p1,v1,svr) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read,svr2) = (match svr with
            | ShVar(p2,Var(p3,s)) ->
               if (s = v) then (true,ShVar(p2,Var(p3,new_prefix))) else (false,svr)
            | _ -> (false,svr)) in
         let new_inst = SllInstr(p1,v2,svr2) in
         let new_k = if (read || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if read then header::l3 else l3 in
         (l@l4,new_k)
      | SrlInstr(p1,v1,svr) ->
         let (write,v2) = (match v1 with
            | Var(p2,s) -> if (s = v) then (true,Var(p2,new_prefix)) else (false,v1)
            | _ -> (false,v1)) in
         let (read,svr2) = (match svr with
            | ShVar(p2,Var(p3,s)) ->
               if (s = v) then (true,ShVar(p2,Var(p3,new_prefix))) else (false,svr)
            | _ -> (false,svr)) in
         let new_inst = SrlInstr(p1,v2,svr2) in
         let new_k = if (read || write) then k+1 else k in
         let l1 = [] in
         let l2 = if write then footer::l1 else l1 in
         let l3 = new_inst::l2 in
         let l4 = if read then header::l3 else l3 in
         (l@l4,new_k)
      | _ -> (l@[i],k)
   ) ([],0) il in result
;;