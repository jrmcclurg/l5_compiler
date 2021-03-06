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
 * Contains the "spill", "liveness", and "graph" helper
 * functions, along with the l2-to-l1 compilation
 * functionality.
 *)

open L2_ast;;
open Utils;;
open Flags;;

(*********************************************************
 **  LIVENESS                                           **
 *********************************************************)

(* compares two variables (returns 0 iff they are equal) *)
(*let compare_var (v1 : var) (v2 : var) : int =
   compare (get_var_id v1) (get_var_id v2)
;;*)

(*module VarSet = Set.Make(struct 
                            type t = var
                            let compare = compare_var
                         end);;*)

module IntSet = Set.Make(struct 
                            type t = int
                            let compare = (Pervasives.compare : (int -> int -> int))
                         end);;

(* prints a list of ints *)
let print_int_list (vl : int list) = 
   print_string "[";
   List.iter (fun v -> print_int v; print_string ", ") vl;
   print_string "]"
;;

let print_var_set (vs : IntSet.t) = 
   print_string "[";
   IntSet.iter (fun v -> print_string (get_symbol v); print_string ", ") vs;
   print_string "]"
;;

(* prints a list of vars *)
let print_var_list (vl : var list) = 
      List.iter (fun v -> print_var v; print_string " ") vl;
      print_string "\n"
;;

(* print a list of (var list) *)
let print_vars_list vls sp =
   List.iter (fun vl ->
      print_string "(";
      List.iter (fun v -> 
         print_var v;
         print_string " "
      ) vl;
      print_string (")"^sp);
   ) vls
;;

(*
(*
 * find_target_ins_helper il s1 s2o
 *
 * Gets a list of all "ins" for a given label instruction
 *
 * il   - the instruction list
 * s1   - the label to search for
 * s2o  - an optional second label to search for
 *
 * returns a var list of all the "ins" (no duplicates, list not sorted)
 *)
let rec find_target_ins_helper (il : (instr * IntSet.t * IntSet.t) list) (s1 : int) (s2o : int option) : IntSet.t =
   let find_target_ins_helper_fun = (fun res (i1,ins,_) ->
      match (i1,s2o) with
      | (LabelInstr(_,s),None) -> if (s1 = s) then (num_unions := !num_unions+1; IntSet.union ins res) else res
      | (LabelInstr(_,s),Some(s2)) -> if ((s1 = s) || (s2 = s)) then (num_unions := !num_unions+1; IntSet.union ins res) else res
      | _ -> res
   ) in
   List.fold_left find_target_ins_helper_fun IntSet.empty il

(* gets the "ins" for a specified target label (see the find_target_ins_helper function)
 * (resulting list is SORTED) *)
and find_target_ins (il : (instr * IntSet.t * IntSet.t) list) (s1 : int) (s2o : int option)
                    (jumps : (int,IntSet.t) Hashtbl.t): IntSet.t =
   let r1 = (try Hashtbl.find jumps s1
            with _ -> IntSet.empty) in
   match s2o with
   | None -> r1
   | Some(s) ->
      (try IntSet.union (Hashtbl.find jumps s) r1
       with _ -> r1)
;;
*)

(* given instruction i, returns (gens, kills) *)
let regs1 = List.fold_right IntSet.add [eax_id;edx_id;ecx_id] IntSet.empty;;
let regs2 = List.fold_right IntSet.add [eax_id;ebx_id;ecx_id;edx_id] IntSet.empty;;
let regs4 = List.fold_right IntSet.add [eax_id;edx_id;ecx_id;edi_id;esi_id] IntSet.empty;;
let regs5 = List.fold_right IntSet.add [eax_id;ecx_id;edi_id;edx_id;esi_id] IntSet.empty;;
let regs6 = List.fold_right IntSet.add [eax_id;edi_id;esi_id] IntSet.empty;;
let get_gens_kills (i : instr) : (IntSet.t * IntSet.t) =
   match i with
   (* assignment *)
   | AssignInstr(_,VarOrReg(_,v,_),VarSVal(_,VarOrReg(_,v2,_))) -> (IntSet.singleton v2, IntSet.singleton v)
   | AssignInstr(_,VarOrReg(_,v,_),_) -> (IntSet.empty, IntSet.singleton v)
   (* mem read *)
   | MemReadInstr(_,VarOrReg(_,v1,_),VarOrReg(_,v2,_),_) -> (IntSet.singleton v2,IntSet.singleton v1)
   (* mem write *)
   | MemWriteInstr(_,VarOrReg(_,v1,_),_,VarSVal(_,VarOrReg(_,v2,_))) -> (IntSet.add v2 (IntSet.singleton v1),IntSet.empty)
   | MemWriteInstr(_,VarOrReg(_,v1,_),_,_) -> (IntSet.singleton v1,IntSet.empty)
   (* plus *)
   | PlusInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_))) -> (IntSet.add v2 (IntSet.singleton v),IntSet.singleton v)
   | PlusInstr(_,VarOrReg(_,v,_),_) -> (IntSet.singleton v, IntSet.singleton v)
   (* minus *)
   | MinusInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_))) -> (IntSet.add v2 (IntSet.singleton v),IntSet.singleton v)
   | MinusInstr(_,VarOrReg(_,v,_),_) -> (IntSet.singleton v, IntSet.singleton v)
   (* times *)
   | TimesInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_))) -> (IntSet.add v2 (IntSet.singleton v),IntSet.singleton v)
   | TimesInstr(_,VarOrReg(_,v,_),_) -> (IntSet.singleton v, IntSet.singleton v)
   (* bitwise and *)
   | BitAndInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_))) -> (IntSet.add v2 (IntSet.singleton v),IntSet.singleton v)
   | BitAndInstr(_,VarOrReg(_,v,_),_) -> (IntSet.singleton v, IntSet.singleton v)
   (* shift left *)
   | SllInstr(_,VarOrReg(_,v,_),ShVar(_,VarOrReg(_,v2,_))) -> (IntSet.add v2 (IntSet.singleton v),IntSet.singleton v)
   | SllInstr(_,VarOrReg(_,v,_),_) -> (IntSet.singleton v, IntSet.singleton v)
   (* shift right *)
   | SrlInstr(_,VarOrReg(_,v,_),ShVar(_,VarOrReg(_,v2,_))) -> (IntSet.add v2 (IntSet.singleton v),IntSet.singleton v)
   | SrlInstr(_,VarOrReg(_,v,_),_) -> ((IntSet.singleton v), (IntSet.singleton v))
   (* less-than comparison *)
   | LtInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_)),VarTVal(_,VarOrReg(_,v3,_))) ->
      (IntSet.add v3 (IntSet.singleton v2),(IntSet.singleton v))
   | LtInstr(_,VarOrReg(_,v,_),_,VarTVal(_,VarOrReg(_,v3,_))) -> ((IntSet.singleton v3),(IntSet.singleton v))
   | LtInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_)),_) -> ((IntSet.singleton v2),(IntSet.singleton v))
   | LtInstr(_,VarOrReg(_,v,_),_,_) -> (IntSet.empty, (IntSet.singleton v))
   (* less-than-or-equal-to comparison *)
   | LeqInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_)),VarTVal(_,VarOrReg(_,v3,_))) ->
      (IntSet.add v3 (IntSet.singleton v2),(IntSet.singleton v))
   | LeqInstr(_,VarOrReg(_,v,_),_,VarTVal(_,VarOrReg(_,v3,_))) -> ((IntSet.singleton v3),(IntSet.singleton v))
   | LeqInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_)),_) -> ((IntSet.singleton v2),(IntSet.singleton v))
   | LeqInstr(_,VarOrReg(_,v,_),_,_) -> (IntSet.empty, (IntSet.singleton v))
   (* equal-to comparison *)
   | EqInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_)),VarTVal(_,VarOrReg(_,v3,_))) ->
      (IntSet.add v3 (IntSet.singleton v2),(IntSet.singleton v))
   | EqInstr(_,VarOrReg(_,v,_),_,VarTVal(_,VarOrReg(_,v3,_))) -> ((IntSet.singleton v3),(IntSet.singleton v))
   | EqInstr(_,VarOrReg(_,v,_),VarTVal(_,VarOrReg(_,v2,_)),_) -> ((IntSet.singleton v2),(IntSet.singleton v))
   | EqInstr(_,VarOrReg(_,v,_),_,_) -> (IntSet.empty, (IntSet.singleton v))
   (* label *)
   | LabelInstr(_,_) -> (IntSet.empty,IntSet.empty)
   (* goto *)
   | GotoInstr(_,_) -> (IntSet.empty,IntSet.empty)
   (* less-than jump *)
   | LtJumpInstr(_,VarTVal(_,VarOrReg(_,v1,_)),VarTVal(_,VarOrReg(_,v2,_)),_,_) ->
      (IntSet.add v2 (IntSet.singleton v1),IntSet.empty)
   | LtJumpInstr(_,_,VarTVal(_,VarOrReg(_,v2,_)),_,_) -> ((IntSet.singleton v2),IntSet.empty)
   | LtJumpInstr(_,VarTVal(_,VarOrReg(_,v1,_)),_,_,_) -> ((IntSet.singleton v1),IntSet.empty)
   (* less-than-or-equal-to jump *)
   | LeqJumpInstr(_,VarTVal(_,VarOrReg(_,v1,_)),VarTVal(_,VarOrReg(_,v2,_)),_,_) ->
      (IntSet.add v2 (IntSet.singleton v1),IntSet.empty)
   | LeqJumpInstr(_,_,VarTVal(_,VarOrReg(_,v2,_)),_,_) -> ((IntSet.singleton v2),IntSet.empty)
   | LeqJumpInstr(_,VarTVal(_,VarOrReg(_,v1,_)),_,_,_) -> ((IntSet.singleton v1),IntSet.empty)
   (* equal-to jump *)
   | EqJumpInstr(_,VarTVal(_,VarOrReg(_,v1,_)),VarTVal(_,VarOrReg(_,v2,_)),_,_) ->
      (IntSet.add v2 (IntSet.singleton v1),IntSet.empty)
   | EqJumpInstr(_,_,VarTVal(_,VarOrReg(_,v2,_)),_,_) -> ((IntSet.singleton v2),IntSet.empty)
   | EqJumpInstr(_,VarTVal(_,VarOrReg(_,v1,_)),_,_,_) -> ((IntSet.singleton v1),IntSet.empty)
   (* call *)
   | CallInstr(_,VarUVal(p,VarOrReg(_,v,_))) ->
      let l = IntSet.add v regs1 in
      (l,regs2)
   | CallInstr(p,_) ->
      (regs1,regs2)
   (* tail-call *)
   | TailCallInstr(_,VarUVal(p,VarOrReg(_,v,_))) ->
      let l = IntSet.add v regs4 in
      (l,IntSet.empty)
   | TailCallInstr(p,_) -> (regs5,IntSet.empty)
   (* return *)
   | ReturnInstr(p) -> (regs6,IntSet.empty)
   (* print *)
   | PrintInstr(p,VarTVal(_,VarOrReg(_,v,_))) -> ((IntSet.singleton v),regs1)
   | PrintInstr(p,_) -> (IntSet.empty,regs1)
   (* allocate *)
   | AllocInstr(p,VarTVal(_,VarOrReg(_,v2,_)),VarTVal(_,VarOrReg(_,v3,_))) ->
      (IntSet.add v3 (IntSet.singleton v2),regs1)
   | AllocInstr(p,_,VarTVal(_,VarOrReg(_,v3,_))) ->
      ((IntSet.singleton v3),regs1)
   | AllocInstr(p,VarTVal(_,VarOrReg(_,v2,_)),_) ->
      ((IntSet.singleton v2),regs1)
   | AllocInstr(p,_,_) -> (IntSet.empty,regs1)
   (* array-error *)
   | ArrayErrorInstr(p,VarTVal(_,VarOrReg(_,v2,_)),VarTVal(_,VarOrReg(_,v3,_))) ->
      (IntSet.add v3 (IntSet.singleton v2),regs1)
   | ArrayErrorInstr(p,_,VarTVal(_,VarOrReg(_,v3,_))) ->
      ((IntSet.singleton v3),regs1)
   | ArrayErrorInstr(p,VarTVal(_,VarOrReg(_,v2,_)),_) ->
      ((IntSet.singleton v2),regs1)
   | ArrayErrorInstr(p,_,_) -> (IntSet.empty,regs1)
   | _ -> (IntSet.empty,IntSet.empty)
;;

(*
 * compute_ins gens kills outs
 *
 * Computes the "ins" using the formula
 * ins = gens U (outs - kills)
 * (where "U" is set union)
 * The result is sorted
 *)
let compute_ins (gens : IntSet.t) (kills : IntSet.t) (outs : IntSet.t) : IntSet.t =
   IntSet.union gens (IntSet.diff outs kills)
;;

(*
 * liveness_helper il
 * 
 * A fixpoint operator which iteratively updates the "ins" and "outs" for
 * each instruction until no change is seen
 * 
 * il - the list of tuples (i, ins, outs) where i is an instruction
 *                                              ins is the current in list
 *                                              outs is the current out list
 * 
 * returns a list of tuples (i, ins, outs) having the final results
 *)
let rec liveness_helper (il : (int,(instr * IntSet.t * IntSet.t * IntSet.t * IntSet.t * bool)) Hashtbl.t) (currents : IntSet.t) : unit =
   (*print_string "liveness_helper: currents = ";
   print_int_list currents;
   print_string "\n";*)
   (* go through the instructions *)
   let (change,new_currents) = IntSet.fold (fun c (flag,res) ->
      (*print_string ("current: "^(string_of_int c)^"\n");*)
      let (i,ins,outs,prevs,nexts,processed) = Hashtbl.find il c in (* TODO - what if error? *)
      let prev_ins = IntSet.fold (fun p res ->
         let (_,ins,_,_,_,_) = Hashtbl.find il p in
         IntSet.union ins res
      ) nexts IntSet.empty in
   (*print_string ("   current "^(string_of_int c)^" : prev ins: ");
   print_var_set prev_ins;
   print_string "\n";*)
      (* get the gens and kills for this instruction *)
      let (gens,kills) = get_gens_kills i in
      (* compute the new "ins" list *)
      let new_ins = compute_ins gens kills prev_ins in
      (* compute the new "outs" list as the union of the "ins" of
       * the successor instruction(s) *)
      let new_outs = prev_ins in
      if processed && (IntSet.equal new_ins ins) && (IntSet.equal new_outs outs) then
         (flag,res)
      else (
       Hashtbl.replace il c (i,new_ins,new_outs,prevs,nexts,true);
       (true,IntSet.union prevs res)
      )
   ) currents (false,IntSet.empty) in
   (* if the "ins" or "outs" changed, process again, otherwise we're done *)
   if change then liveness_helper il new_currents;
;;

(*
 * liveness il
 * 
 * Given a list of instructions, returns the "in" and "out" lists
 * (liveness analysis).
 *
 * il - the (instr list) containing the instructions
 *
 * returns (l1, l2) where l1 is a (var list) of the ins and
 *                        l2 is a (var list) of the outs
 *)
let liveness (il : instr list) : ((instr * IntSet.t * IntSet.t) list) = 
   let jumps = ((Hashtbl.create 100) : (int, IntSet.t) Hashtbl.t) in (* TODO - size? *)
   let labels = ((Hashtbl.create 100) : (int, int) Hashtbl.t) in (* TODO - size? *)
   let get_jumps = (fun (s : int) -> try Hashtbl.find jumps s with _ -> IntSet.empty) in
   let add_jump = (fun (s : int) (index : int) ->
      Hashtbl.replace jumps s (IntSet.add index (get_jumps s))
   ) in
   let _ = List.fold_left (fun k i ->
      (match i with
      | LabelInstr(_,s) -> Hashtbl.replace labels s k
      | GotoInstr(_,s) -> add_jump s k
      | LtJumpInstr(_,_,_,s1,s2) -> add_jump s1 k; add_jump s2 k
      | LeqJumpInstr(_,_,_,s1,s2) -> add_jump s1 k; add_jump s2 k
      | EqJumpInstr(_,_,_,s1,s2) -> add_jump s1 k; add_jump s2 k
      | _ -> () );
      (k + 1)
   ) 0 il in ();
   let itable = ((Hashtbl.create 100) : (int, (instr * IntSet.t * IntSet.t * IntSet.t * IntSet.t * bool)) Hashtbl.t) in (* TODO - size? *)
   let len = List.length il in
   let _ = List.fold_left (fun (k,prev) i ->
      (match i with
      | GotoInstr(_,s) ->
         Hashtbl.replace itable k (i,IntSet.empty,IntSet.empty,prev,IntSet.singleton (Hashtbl.find labels s),false); (k+1,IntSet.singleton k)  (* TODO -errors !!! *)
      | LtJumpInstr(_,_,_,s1,s2) ->
         Hashtbl.replace itable k (i,IntSet.empty,IntSet.empty,prev,IntSet.add (Hashtbl.find labels s1) (IntSet.singleton (Hashtbl.find labels s2)),false); (k+1,IntSet.singleton k)
      | LeqJumpInstr(_,_,_,s1,s2) ->
         Hashtbl.replace itable k (i,IntSet.empty,IntSet.empty,prev,IntSet.add (Hashtbl.find labels s1) (IntSet.singleton (Hashtbl.find labels s2)),false); (k+1,IntSet.singleton k)
      | EqJumpInstr(_,_,_,s1,s2) ->
         Hashtbl.replace itable k (i,IntSet.empty,IntSet.empty,prev,IntSet.add (Hashtbl.find labels s1) (IntSet.singleton (Hashtbl.find labels s2)), false); (k+1,IntSet.singleton k)
      | LabelInstr(_,s) ->
         Hashtbl.replace itable k (i,IntSet.empty,IntSet.empty,IntSet.union prev (get_jumps s),(if k+1==len then IntSet.empty else IntSet.singleton (k+1)), false); (k+1,IntSet.singleton k)
      | ReturnInstr(_) ->
         Hashtbl.replace itable k (i,IntSet.empty,IntSet.empty,prev, IntSet.empty,false); (k+1,IntSet.singleton k)
      | ArrayErrorInstr(_,_,_) ->
         Hashtbl.replace itable k (i,IntSet.empty,IntSet.empty,prev, IntSet.empty,false); (k+1,IntSet.singleton k)
      | TailCallInstr(_,_) ->
         Hashtbl.replace itable k (i,IntSet.empty,IntSet.empty,prev, IntSet.empty,false); (k+1,IntSet.singleton k)
      | _ ->
         Hashtbl.replace itable k (i,IntSet.empty,IntSet.empty,prev, (if k+1==len then IntSet.empty else IntSet.singleton (k+1)),false); (k+1,IntSet.singleton k) );
   ) (0,IntSet.empty) il in ();
   (*Hashtbl.iter (fun k (i,ins,outs,j,next,p) -> 
      print_string (";; Instruction # "^(string_of_int k)^" : ");
      print_instr i;
      print_string ", ";
      print_var_set ins;
      print_string ", ";
      print_var_set outs;
      print_string ", prev = ";
      print_int_list j;
      print_string ", next = ";
      print_int_list next;
      print_string "\n"
   ) itable;*)
   (* add an empty "in" and "out" list for each instruction *)
   (* get the ins and outs (this is a fixpoint operator *)
   liveness_helper itable (if len > 0 then IntSet.singleton (len-1) else IntSet.empty);
   (*print_string ("List length: "^(string_of_int len)^"\n");*)
   let rec to_list = (fun k arr -> 
      if k < 0 then arr else
      let (i,ins,outs,_,_,_) = Hashtbl.find itable k in (* TODO - what if fail? *)
      let arr2 = (i,ins,outs)::arr in
      to_list (k-1) arr2
   ) in
   to_list (len-1) []
;;

(*********************************************************
 **  GRAPH                                              **
 *********************************************************)

(*
 * add_edge v1 v2o h
 *
 * Adds an edge from v1 to v2 in the graph h
 *
 * v1     - the source variable v1
 * v2o    - an optional destination variable
 * h      - the graph
 *
 * If v2o is None, then just a vertex v1 is added to the
 * graph.  The graph is represented as a hashtable mapping
 * source vertex names s to pairs (v,dests) where v is the
 * var corresponding to the name s, and dests is a
 * hashtable of destination vertices (more specifically,
 * dests is a hashtable mapping vertex names to their
 * corresponding vars).
 *)
let all_the_edges = ref 0;;
let add_edge (id : int) (v2o : int option)
                  (h : (int, IntSet.t) Hashtbl.t) : unit =
   (*print_string "add_edge(";
   print_int id;
   (match v2o with
   | Some(x) -> print_string (", "^(string_of_int x)^"")
   | _ -> ());
   print_string ")\n"; *)
   (* leave ebp/esp registers out of the graph *)
   if id == ebp_id then ()
   else if id == esp_id then ()
   else (
   (* process registers other than ebp/esp... *)
   (* get the name of v1 *)
   let t = (
      (* see if there's a source vertex for "name" in the graph
       * (if there is, "t" will be bound to its table
       * of destinations) *)
      try Hashtbl.find h id
      with _ ->
         (* if there's no source vertex "id" in the graph, add one,
          * along with an empty table for destination vertices *)
         let t2 = IntSet.empty in
         Hashtbl.replace h id t2;
         t2
   ) in (
   match v2o with
   | Some(id2) ->
      (* ignore v2o if it is ebp/esp *)
      if id2 == ebp_id then ()
      else if id2 == esp_id then ()
      (* otherwise, if v2o okay... *)
      else if id != id2 then (
      (* get the id of v2 *)
      (* if v2 is a different variable/register than v1, add
       * an edge (v1,v2) by putting v2 in v1's dest table *)
         all_the_edges := !all_the_edges + 1;
         Hashtbl.replace h id (IntSet.add id2 t)
      )
   | _ -> () ))
;;

(*
 * add_all_edges vl1 vl2 so h
 *
 * Add all the edges (v1,v2) to graph h, where
 * v1 is in vl1 and v2 is in vl2.
 *
 * vl1    - a list of source vertices (variables)
 * vl2    - a list of destination vertices (variables)
 * so     - optional edge to ignore
 * h      - the graph
 *
 * Every edge having a source in vl1 and destination in vl2
 * is added to the graph h, with the exception of the edge
 * (u,v) if so = Some((u,v)), in which case u and v are just
 * added as vertices in h.  The graph h has the same structure
 * as the "h" parameter of the add_edge function.
 *)
let add_all_edges_helper (vl1 : IntSet.t) (vl2 : IntSet.t) (so : (int * int) option)
                         (h : (int, IntSet.t) Hashtbl.t) (reverse : bool) : unit =
   (* if vl1 is empty, just add a vertex for each item in vl2 *)
   match (IntSet.is_empty vl1) with
   | true -> IntSet.iter (fun v2 -> add_edge v2 None h) vl2
   | _ ->
   (* if vl1 is non-empty, iterate through its items *)
   IntSet.iter (fun s1 ->
      (match (IntSet.is_empty vl2) with
      (* if vl2 is empty, just add a vertex for the current item of vl1 *)
      | true -> add_edge s1 None h
      | _ ->
         (* if vl2 is non-empty, iterate through its items *)
         IntSet.iter (fun s2 ->
            (* get the ids for v1/v2 *)
            (match so with
            (* if there's an edge we want to ignore... *)
            | Some(s1t,s2t) ->
               (* if (v1,v2) matches the ignored edge, then
                * just add disconnected vertices v1 and v2 *)
               if (((s1==s1t) && (s2==s2t)) || ((s1==s2t) && (s2==s1t))) then (
                  add_edge s1 None h;
                  add_edge s2 None h;
               )
               (* if (v1,v2) is not the ignored edge... *)
               else (
                  (* add the edges (v1,v2) and (v2,v1) *)
                  if s1 == s2 then add_edge s1 None h else (
                     add_edge s1 (Some(s2)) h;
                     if reverse then add_edge s2 (Some(s1)) h
                  )
               )
            (* if there's no edge we want to ignore... *)
            | _ -> 
               (* add the edges (v1,v2) and (v2,v1) *)
               if s1 == s2 then add_edge s1 None h else (
                  add_edge s1 (Some(s2)) h;
                  if reverse then add_edge s2 (Some(s1)) h
               )
            )
         ) vl2 )
   ) vl1
;;

let add_all_edges (vl1 : IntSet.t) (vl2 : IntSet.t) (so : (int * int) option)
                  (h : (int, IntSet.t) Hashtbl.t) : unit =
   add_all_edges_helper vl1 vl2 so h true
;;

(*
 * compute_adjacency_table il h first
 *
 * Given an empty graph h, adds all the appropriate
 * edges for the graph coloring analysis, based on a
 * list of instructions il.
 *
 * il    - the list of instructions
 * h     - an empty graph to populate
 * first - whether this is the first call (rather
 *         than a recursive one)
 *
 * The il should have the same structure as the instruction
 * list returned by the liveness analysis in the
 * liveness_helper function.  The (initially empty) graph h
 * should have the same format as the "h" argument to the
 * add_edge function.  The "first" argument should be true
 * when this function is called normally.
 *)
(* l1 is all the usable registers except ecx *)
let l1_adj = (List.fold_right IntSet.add [eax_id;ebx_id;edi_id;edx_id;esi_id] IntSet.empty);;
(* l2 is the callee-save registers *)
let l2_adj = (List.fold_right IntSet.add [edi_id;esi_id] IntSet.empty);;
let rec compute_adjacency_table (il : (instr * IntSet.t * IntSet.t) list)
                                (h : (int, IntSet.t) Hashtbl.t)
                                : unit =
   (*let num = List.length il in*)
   let _ = List.fold_left (fun (first,n) (i,ins,outs) ->
      all_the_edges := 0;
      flush stdout;
      (* "temp" is a potential edge to ignore when generating the graph *)
      let temp = (match i with
      (* if this instruction is a <- b, then a,b don't conflict, so
       * we want to ignore the edge (a,b) in the graph *)
      | AssignInstr(_,VarOrReg(_,v1,_),VarSVal(_,VarOrReg(_,v2,_))) -> Some((v1,v2))
      (* for any other instructions, we don't ignore the edge *)
      | _ -> None ) in
      (* add edges between variables that are live at the same time
       * (this means any variables that appear in any "out" set together,
       * or any variables that appear together in the first instruction's
       * "in" set) *)
      if first then add_all_edges_helper ins ins None h false else add_all_edges ins (IntSet.empty) None h;
      add_all_edges_helper outs outs temp h false;
      (* add edges between the kills and the out set *)
      let (gens,kills) = get_gens_kills i in
      (*print_string ("computing "^(string_of_int n)^"/"^(string_of_int num)^
         ": first="^(if first then "yes" else "no")^" ins="^(string_of_int (IntSet.cardinal ins))^
         " outs="^(string_of_int (IntSet.cardinal outs))^
         " gens="^(string_of_int (IntSet.cardinal gens))^" kills="^(string_of_int (IntSet.cardinal kills))^
         " num_added="^(string_of_int !all_the_edges)^"\n");*)
      (* NOTE: we don't need to add vertices for the gens, since all the gens
       * except for that of the first instruction go into the outs of previous
       * instructions.  The gens for the first instruction are capture by the ins
       * of the first instruction. *)
      add_all_edges kills outs temp h;
      (* handle the special instructions *)
      (match i with
      (* any shift variable v will conflict with all usable registers except ecx
       * (since ecx is the only allowable shift register in the x86 instruction) *)
      | SllInstr(_,_,ShVar(_,(VarOrReg(_,v,true)))) -> add_all_edges (IntSet.singleton v) l1_adj None h
      | SrlInstr(_,_,ShVar(_,(VarOrReg(_,v,true)))) -> add_all_edges (IntSet.singleton v) l1_adj None h
      (* a destination variable for comparisons will conflict with the 
       * callee-save registers, since the callER-save registers are the only
       * valid destinations *)
      | LtInstr(_,(VarOrReg(_,v,true)),_,_) -> add_all_edges (IntSet.singleton v) l2_adj None h
      | LeqInstr(_,(VarOrReg(_,v,true)),_,_) -> add_all_edges (IntSet.singleton v) l2_adj None h
      | EqInstr(_,(VarOrReg(_,v,true)),_,_) -> add_all_edges (IntSet.singleton v) l2_adj None h
      | _ -> ());
      (false,n+1)
      (* process the remaining instructions *)
   ) (true,1) il in ()
;;

let estimate_spill_num edges max_edges diff i num_sources = match !spill_mode with
   | SpillMin -> 1
   | SpillMax -> i
   (*| SpillConst(c) -> max 1 (min c i)
   | SpillPercent(p) -> max 1 (min (int_of_float (ceil (p*.(float_of_int diff)))) diff)*)
   | SpillDampedDiff ->
      (int_of_float ((float_of_int diff) /.
         ((float_of_int num_sources)/.((float_of_int num_sources)**(1.0 -. ((float_of_int i)/.(float_of_int num_sources)))))))
   | SpillIncrease -> min i edges
   | SpillHalve(k) -> min ((k - 1) * i * max_edges / num_sources) edges (* the (k -1) causes a "halving" by a factor of 1/k *)
;;

(*
 * graph_color il
 *
 * Performs graph coloring based on a given instruction list il.

 * The graph is returned as an adjacency table "at" which is
 * structured as a list of tuples (src,dest1,dest2,dest3,...)
 * representing the edges from src to various destinations.
 *
 * returns (at,colors,ok) where
 * "at" is the adjacency table representing the graph,
 * "colors" is the list of (var,reg) coloring assignments, and
 * "ok" is true iff the graph was able to be colored properly
 *)
let graph_color (il : instr list) : ((int * IntSet.t) list * (int * int) list * bool * int) =
   (* perform the liveness analysis based on the instruction list *)
   if !debug_2 then (
      print_string ("Liveness... ");
      flush stdout
   );
   let il2 = liveness il in
   if !debug_2 then (
      print_string ("done.\n");
      flush stdout
   );
   (* make sure all of the usable registers are connected *)
   let l1 = List.fold_right IntSet.add
            [eax_id;ebx_id;ecx_id;edi_id;edx_id;esi_id] IntSet.empty in
   (* create an empty hashtable for the graph *)
   let h = ((Hashtbl.create (List.length il2)) : (int, IntSet.t) Hashtbl.t) in (* TODO - size? *)
   (* add edges between all the usable registers *)
   if !debug_2 then (
      print_string ("Edges... ");
      flush stdout
   );
   add_all_edges l1 l1 None h;
   if !debug_2 then (
      print_string ("done.\n");
      flush stdout
   );
   (* populate h with the conflict graph *)
   if !debug_2 then (
      print_string ("Computing graph ("^(string_of_int (List.length il2))^" instr)... ");
      flush stdout
   );
   compute_adjacency_table il2 h;
   if !debug_2 then (
      print_string ("done.\n");
      flush stdout
   );
   (* find all the source vertices in graph h *)
   if !debug_2 then (
      print_string ("Sorting... ");
      flush stdout
   );
   let keys = Hashtbl.fold (fun k tab res -> 
      (k,tab)::res
   ) h [] in
   (* sort the source vertices by (ascending order of) number of conflicts *)
   let keyst = List.sort (fun (a,at) (b,bt) ->
      (Pervasives.compare : (int -> int -> int)) (IntSet.cardinal bt) (IntSet.cardinal at)) keys in (* XXX *)
   let keys2 = List.map (fun (k,tab) -> k) keyst in
   let num_sources = List.length keys2 in
   let max_edges = (match keyst with
   | (a,at)::b -> IntSet.cardinal at
   | _ -> 0) in
   (* now we do the heuristic graph coloring *)
   (* create a hashtable for mapping variable ids to their register (color) assignments *)
   let assignments = ((Hashtbl.create (IntSet.cardinal l1)) : (int,int) Hashtbl.t) in
   (* go through the graph (via the sorted keys2 list)
    * and compute the return values (ag,colors,ok) *)
   if !debug_2 then (
      print_string ("done.\n");
      flush stdout
   );
   let (ag,colors,ok,the_max,the_num,_,_,_) =
   List.fold_left (fun (r2,r3,flag,the_max_local,the_num_local,the_prev_local,the_prev_max_local,the_counter_local) x -> 
      (* find the current source variable "x" in the graph
       * (v is the corresponding var data structure, and 
       * tb is the hashtable of destinations) *)
      (* get the list of destination variables *)
      let tbl = Hashtbl.find h x in
      let test = IntSet.cardinal tbl in
      let the_max_local_2 = if test > the_max_local then test else the_max_local in
      let diff = max 0 (the_prev_local - test) in
      let check = (max 0 (estimate_spill_num test max_edges diff (the_counter_local+1) num_sources)) in
      if !debug_spill then (
         print_string ((string_of_int (the_counter_local+1))^"/"^(string_of_int num_sources)^
                       ". Edges: "^(string_of_int test)^" diff = "^(string_of_int diff)^" (max = "^
                       (string_of_int max_edges)^") (est = "^(string_of_int check)^")\n");
         flush stdout
      );
      let the_num_local_2 = if check > the_prev_max_local then the_counter_local else the_num_local in
      let the_prev_max_local_2 = if check > the_prev_max_local then check else the_prev_max_local in
      let the_prev_local_2 = test in
      let the_counter_local_2 = the_counter_local + 1 in
      (* go through all of the usable registers l1, 
       * and compute an optional color (register)
       * assignment l2 *)
      let l2 = IntSet.fold (fun the_id r ->
         (* the_id is the current register id *)
         (* check if "r" already contains a coloring *)
         match r with
         (* if "r" does not contain a coloring yet... *)
         | None ->
            (* go through the list tbl of destination vertices to see
             * if register the_id is contained there *)
            let found = (IntSet.fold (fun t flag ->
               let f = 
               (
               (* if this destination vertex is a variable... *)
               if (not (is_register t)) then
                  (* look it up in the assigned reg table *)
                  (try let test = Hashtbl.find assignments t in (test == the_id)
                  with _ -> false)
               else
               (* if this destination vertex is a register... *)
               if (t == the_id) then true else false) in
               (flag || f)
            ) tbl false) in
            (* if register the_id was found in the dest list,
             * we can't used it as the coloring assignment *)
            if found then None
            (* otherwise, if the_id was NOT found, we can use
             * it as a coloring assignment (and add it to the
             * table of assignments) *)
            else (
               Hashtbl.add assignments x the_id;
               (Some(the_id))
            )
         (* if "r" already contains a coloring, just use that one *)
         | Some(_) -> r
      ) l1 None in

      (* based on the current source vertex v, compute newl,
       * the updated list of coloring assignments, and
       * f, the updated status of the coloring (true iff successful
       * coloring) *)
      let (newl,f) = (
      (* if the current source vertex is a variable... *)
      if (not (is_register x)) then (
         (* if we found a valid coloring for v, update the list of
          * coloring assignments *)
         (match l2 with
         | Some(c) -> (r3@[(x,c)],true)  (* TODO - this is probably slow *)
         | _ -> (r3,false) ) )
      (* if the current source vertex is a REGISTER, we don't need
       * to add a register assignment *)
      else (r3,true)) in
      (* add the row (v,dest1,dest2,dest3,...) to the adjacency
       * table, where [dest1;dest2;dest] is the sorted version of
       * destination list tbl.  also update the coloring assignment
       * list (newl) and the result status (f && flag) which is
       * true iff ALL source vertices are able to be assigned a
       * color properly *)
      (r2@[(x,tbl)],newl,f && flag,the_max_local_2,the_num_local_2,the_prev_local_2,the_prev_max_local_2,the_counter_local_2)
   ) ([],[],true,0,0,0,0,0) keys2 in
   let num_to_spill = max 1 (min the_num the_max) in
   if !debug_spill then (
      print_string ("Max edges: "^(string_of_int the_max)^" (spill estimate: "^(string_of_int num_to_spill)^")\n");
      flush stdout
   );
   (ag,colors,ok,num_to_spill)
;;

(*********************************************************
 **  SPILL                                              **
 *********************************************************)

(*
 * spill il v off prefix
 * 
 * Given a list of instructions, returns a new list of instructions
 * with the specified variable spilled to memory.
 *
 * il     - the (instr list) containing the instructions
 * v      - the variable to spill
 * off    - the offset in memory to spill to
 * prefix - the prefix for any temporary variables generated
 *
 * returns l1, an (instr list) with the variabled spilled properly
 *)
let rec spill (il : instr list) (v : int) (off : int32) (prefix : string) : instr list =
   (* go through the list of instructions... *)
   let (result,_) = List.fold_left (fun (l,k) i -> (* l is the cumulative list, k is the unique number,
                                                    * and i is the current instruction to process *)
      let p = get_pos_instr i in (* the the Pos of the instruction *)
      let new_prefix = add_symbol (prefix^(string_of_int k)) in (* compute a unique variable name *)
      let header = MemReadInstr(p,VarOrReg(p,new_prefix,true),VarOrReg(p,ebp_id,false),off) in (* a 'header' instruction (i.e. one that
                                                                       * does (unique_var <- (mem ebp offset)) *)
      let footer = MemWriteInstr(p,VarOrReg(p,ebp_id,false),off,
                                   VarSVal(p,VarOrReg(p,new_prefix,true))) in (* a 'footer' instruction (i.e.
                                                                     * one that does
                                                                     * ((mem ebp offset) <- unique_var)) *)
      (* check to see what instruction we have *)
      match i with
      (* (v1 <- sv) *)
      | AssignInstr(p1,v1,sv) ->
         (* if v1 is equal to the spill variable, the new instruction (i1) will be ((mem ebp offset) <- sv) *)
         let (write,i1,s1) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then
               (true,MemWriteInstr(p2,VarOrReg(p2,ebp_id,false),off,sv),Some(s)) else (false,i,None)
            | _ -> (false,i,None)) in
         (* if sv is equal to the spill variable, the new instruction (i2) will be (v1 <- (mem ebp offset)) *)
         let (read,i2,s2) = (match sv with
            | VarSVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then
                  (true,MemReadInstr(p3,v1,VarOrReg(p3,ebp_id,false),off),Some(s)) else (false,i,None)
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
         (* (l@l1,k) *)
         (List.rev_append l1 l,k)
      (* (v1 <- (mem v2 i)) *)
      | MemReadInstr(p1,v1,v2,i) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v3) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if v2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,v4) = (match v2 with
            | VarOrReg(p2,s,true) ->
               if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v2)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* ((mem v1 i) <- v2) *)
      | MemWriteInstr(p1,v1,i,sv) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if sv2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,sv2) = (match sv with
            | VarSVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarSVal(p2,VarOrReg(p3,new_prefix,true))) else (false,sv)
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
         (*(l@l3,new_k)*)
         (List.rev_append l3 l,new_k)
      (* (v1 += t) *)
      | PlusInstr(p1,v1,t) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,t2) = (match t with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* (v1 -= t) *)
      | MinusInstr(p1,v1,t) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,t2) = (match t with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* (v1 *= t) *)
      | TimesInstr(p1,v1,t) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,t2) = (match t with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* (v1 &= t) *)
      | BitAndInstr(p1,v1,t) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,t2) = (match t with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* (v1 <<= svr) *)
      | SllInstr(p1,v1,svr) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if svr is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,svr2) = (match svr with
            | ShVar(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,ShVar(p2,VarOrReg(p3,new_prefix,true))) else (false,svr)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* (v1 >>= svr) *)
      | SrlInstr(p1,v1,svr) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if svr is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read,svr2) = (match svr with
            | ShVar(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,ShVar(p2,VarOrReg(p3,new_prefix,true))) else (false,svr)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* (v1 <- t1 < t2) *)
      | LtInstr(p1,v1,t1,t2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t2)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* (v1 <- t1 <= t2) *)
      | LeqInstr(p1,v1,t1,t2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t2)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* (v1 <- t1 = t2) *)
      | EqInstr(p1,v1,t1,t2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (write,v2) = (match v1 with
            | VarOrReg(p2,s,true) -> if (s == v) then (true,VarOrReg(p2,new_prefix,true)) else (false,v1)
            | _ -> (false,v1)) in
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t2)
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
         (*(l@l4,new_k)*)
         (List.rev_append l4 l,new_k)
      (* (cjump t1 < t2 s1 s2) *)
      | LtJumpInstr(p1,t1,t2,s1,s2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t2)
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
         (*(l@l3,new_k)*)
         (List.rev_append l3 l,new_k)
      (* (cjump t1 <= t2 s1 s2) *)
      | LeqJumpInstr(p1,t1,t2,s1,s2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t2)
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
         (*(l@l3,new_k)*)
         (List.rev_append l3 l,new_k)
      (* (cjump t1 = t2 s1 s2) *)
      | EqJumpInstr(p1,t1,t2,s1,s2) ->
         (* if v1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t2)
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
         (*(l@l3,new_k)*)
         (List.rev_append l3 l,new_k)
      (* (call u) *)
      | CallInstr(p1,u) ->
         (* if u is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,u2) = (match u with
            | VarUVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarUVal(p2,VarOrReg(p3,new_prefix,true))) else (false,u)
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
         (*(l@l3,new_k)*)
         (List.rev_append l3 l,new_k)
      (* (tail-call u) *)
      | TailCallInstr(p1,u) ->
         (* if u is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,u2) = (match u with
            | VarUVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarUVal(p2,VarOrReg(p3,new_prefix,true))) else (false,u)
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
         (*(l@l3,new_k)*)
         (List.rev_append l3 l,new_k)
      (* (eax <- (print t1)) *)
      | PrintInstr(p1,t1) ->
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t1)
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
         (*(l@l3,new_k)*)
         (List.rev_append l3 l,new_k)
      (* (eax <- (allocate t1 t2)) *)
      | AllocInstr(p1,t1,t2) ->
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t2)
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
         (*(l@l3,new_k)*)
         (List.rev_append l3 l,new_k)
      (* (eax <- (array-error t1 t2)) *)
      | ArrayErrorInstr(p1,t1,t2) ->
         (* if t1 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read1,t3) = (match t1 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t1)
            | _ -> (false,t1)) in
         (* if t2 is equal to the spill variable, it will be replaced by a unique variable name *)
         let (read2,t4) = (match t2 with
            | VarTVal(p2,VarOrReg(p3,s,true)) ->
               if (s == v) then (true,VarTVal(p2,VarOrReg(p3,new_prefix,true))) else (false,t2)
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
         (*(l@l3,new_k)*)
         (List.rev_append l3 l,new_k)
      (*| _ -> (l@[i],k)*)
      | _ -> (List.rev_append [i] l,k)
   ) ([],0) il in List.rev result (* start with an empty list and unique counter "0". return the expanded
                          * list of instructions *)
;;

(*********************************************************
 **  L2-to-L1 CODE GENERATION                           **
 *********************************************************)

let global_spill_count = ref 0;;

(* compile an L2 program into an L1 program *)
let rec compile_program (p : L2_ast.program) : L1_ast.program =
   match p with
   | Program(p,fl) -> 
      let start_time = Sys.time () in
      if !debug_2 || !verbose_mode then (
         print_string ("Compiling L2 to L1..."^(if !verbose_mode then " " else "\n"));
         flush Pervasives.stdout
      );
      (* compile all the functions into L1 functions, giving
       * each one a unique count (starting with 0) *)
      let (_,fl2) = List.fold_left (fun (count,res) f ->
         (count+1,res@[compile_func f count])
      ) (0,[]) fl in
      if (!debug_2 || !debug_stats) then (
         print_string ("Total spill count: "^(string_of_int !global_spill_count)^"\n");
         flush stdout
      );
      (*print_string ("Count:   "^(string_of_int !count)^"\n");*)
      (*print_string ("Num liveness: "^(string_of_int !liveness_num)^"\n");*)
      if !debug_2 || !verbose_mode then (
         let diff = (Sys.time ()) -. start_time in
         print_string ((if !verbose_mode then "" else "...")^"done"^
            (if !verbose_mode then "" else " with L2->L1")^": "^(string_of_float diff)^" sec.\n");
         flush Pervasives.stdout
      );
      L1_ast.Program(p, fl2)

(* compile and L2 function into an L1 function. count should
 * be unique for each function, and should be "0" for the
 * first ("main") function *)
and compile_func (f : L2_ast.func) (count : int) : L1_ast.func = 
   (* check if we're in the first function *)
   let first = (count=0) in
   match f with
   | Function(p,so,il) -> 
   (* TODO XXX - this is a hack to make it work with my wrong
    * test cases.  It can be changed to 1l for normal behavior *)
   let init_offset = 1l in (* number of spots on the stack to allow *)
   let save    = [MemWriteInstr(p,VarOrReg(p,ebp_id,false),Int32.mul init_offset (-4l),VarSVal(p,VarOrReg(p,edi_id,false)));
                  MemWriteInstr(p,VarOrReg(p,ebp_id,false),Int32.sub (Int32.mul init_offset (-4l)) 4l,VarSVal(p,VarOrReg(p,esi_id,false)))] in
   let restore = [MemReadInstr(p,VarOrReg(p,edi_id,false),VarOrReg(p,ebp_id,false),Int32.mul init_offset (-4l));
                  MemReadInstr(p,VarOrReg(p,esi_id,false),VarOrReg(p,ebp_id,false),Int32.sub (Int32.mul init_offset (-4l)) 4l)] in
   (* add save to the front of list, and restore before each tail-call and return *)
   let il2t = List.fold_left (fun res i ->
      match (count,i) with
      | (_,TailCallInstr(_,_)) -> res @ restore @ [i]
      | (_,ReturnInstr(_)) -> res @ restore @ [i]
      | _ -> res @ [i]
   ) save il in
   (* add the edi/esi restore to the end of the first function
    * (presumably the other functions end with return) *)
   let il2 = if first then il2t@restore else il2t in
   (* increase the initial stack size by 2 instructions (for edi/esi save) *)
   let initial = (Int32.add 1l init_offset) in
   (* compile the instructions to L1 instructions *)
   let h = ((Hashtbl.create 64) : (int,unit) Hashtbl.t) in
   let j = ((Hashtbl.create 64) : (int,IntSet.t) Hashtbl.t) in
   let (il3,num_spilled) = compile_instr_list il2 initial count h j in
   global_spill_count := !global_spill_count + (Hashtbl.length h);
   (* add the stack size adjustment to the beginning of each function *)
   let counts = make_counter_list (Int32.mul (Int32.add initial 1l) 4l) (Int32.mul num_spilled 4l) 4l in
   let il4 = (L1_ast.MinusInstr(p,L1_ast.EspReg(p),L1_ast.IntTVal(p, (Int32.mul 4l num_spilled))))::
   (if !clear_uninit then (List.map (fun i -> L1_ast.MemWriteInstr(p,L1_ast.EbpReg(p),Int32.neg i,L1_ast.IntSVal(p,1l))) counts) else [])
   @il3 in
   (* add the stack size de-adjustment to the end of the first instruction *)
   let il5 = if first then
      il4@[L1_ast.PlusInstr(p,L1_ast.EspReg(p),L1_ast.IntTVal(p, (Int32.mul 4l num_spilled)))]
   else il4 in
   L1_ast.Function(p,so,il5)

(* this is a fixpoint operator where i is the current number of spilled vars *)
and compile_instr_list (il : L2_ast.instr list) (num : int32) (count : int) (spilled : (int,unit) Hashtbl.t) (jumps : (int,IntSet.t) Hashtbl.t) :
                                                              (L1_ast.instr list * int32) =
   (* try to do the register allocation *)
   (*if !debug_2 then (print_string ("compile_instr_list: "^(Int32.to_string num)^"\n");
   flush stdout );*)
   let (at,colors,ok,num_to_spill) = graph_color il in
   (*print_string ((Int32.to_string num)^", table size = "^(string_of_int (List.length at))^" : ");
   flush stdout;*)
   (*if (num > 50l) then parse_error "register allocation took too long";*) (* TODO XXX *)
   (* if the graph coloring failed... *)
   if (not ok) then (
      (* just pick any old variable to spill *)
      (*if !debug_spill then ( print_string ("Looking through: "^(string_of_int (List.length at))^"\n");
      flush stdout );*)
      (*print_string ("Table size = "^(string_of_int (List.length at))^"\n");*)
      if !debug_spill then (
         print_string ("Function "^(string_of_int count)^" : spilling "^(string_of_int num_to_spill)^" registers...");
         flush stdout
      );
      let (nameop,il2,ns) = List.fold_left (fun (res,ilt,tnum) (id,vl) -> 
         (*print_var hd;
         print_string "\n";*)
         (* only look at variables we haven't already spilled *)
         if (not (is_register id)) then (
             if (tnum >= num_to_spill) then (res,ilt,tnum) else
             (try Hashtbl.find spilled id; (res,ilt,tnum)
                             with _ -> (
                        let new_num = (Int32.add num (Int32.of_int tnum)) in
                        let spill_name = ("<s_"^(string_of_int count)^"_"^(Int32.to_string new_num)^">") in
                        Hashtbl.replace spilled id ();
                        (*if !debug_spill then ( print_string ("spilling: "^(get_symbol id)^" to "^spill_name^"\n");
                        flush stdout );*)
                        let il2t = spill ilt id (Int32.mul (-4l) (Int32.add new_num (1l))) spill_name in
                             (Some(id),il2t,tnum + 1)
             ) ) ) (* this is the "not already spilled" case *)
	 else (res,ilt,tnum)
      ) (None,il,0) at in
      if !debug_spill then (
         print_string ("done.\n");
         flush stdout
      );
      (* spill and try again *)
      match nameop with
      (* if there's nothing left to spill, fail *)
      | None -> parse_error ("Function "^(string_of_int count)^" : register allocation FAILED!\n") (* TODO don't use parse_error for this message *)
      | Some(id) ->
         let new_num = (Int32.add num (Int32.of_int ns)) in
         (* pick a unique name for the spill variable (it starts with "<" to prevent
          * collisions with normal varialbes) *)
         (*List.iter (fun i -> print_instr i; print_string "\n") il2;*)
         (*print_string "done.\n";
         flush stdout;*)
         (* try to compile again *)
         compile_instr_list il2 new_num count spilled jumps
   )
   (* if the graph coloring succeeded *)
   else (
      if !debug_spill then (
         print_string ("Function "^(string_of_int count)^" : SUCCESS\n");
         flush stdout
      );
      (*print_string ("colored graph properly: "^(string_of_int count)^"\n");*)
      (* set up the replacement table *)
      let h = ((Hashtbl.create (List.length colors)) : (int,L1_ast.reg) Hashtbl.t) in
      List.iter (fun (id,c) -> 
         let r = (
         if c == esi_id then L1_ast.EsiReg(NoPos)
	 else if c == edi_id then L1_ast.EdiReg(NoPos)
	 else if c == ebp_id then L1_ast.EbpReg(NoPos)
	 else if c == esp_id then L1_ast.EspReg(NoPos)
	 else if c == eax_id then L1_ast.CallerSaveReg(NoPos,L1_ast.EaxReg(NoPos))
	 else if c == ecx_id then L1_ast.CallerSaveReg(NoPos,L1_ast.EcxReg(NoPos))
	 else if c == edx_id then L1_ast.CallerSaveReg(NoPos,L1_ast.EdxReg(NoPos))
	 else if c == ebx_id then L1_ast.CallerSaveReg(NoPos,L1_ast.EbxReg(NoPos))
	 else parse_error "invalid register coloring" (* TODO this should never happen *)
	 ) in
	 Hashtbl.replace h id r
      ) colors;
      (List.map (fun i -> compile_instr i h) il, num)
   )

(* compiles an L2 instruction into an L1 instruction. the hashtable
 * has the variable register assignments *)
and compile_instr (i : instr) (h : (int,L1_ast.reg) Hashtbl.t) : L1_ast.instr =
   match i with
   | AssignInstr(p,v,sv) ->
      L1_ast.AssignInstr(p, compile_var v h, compile_sval sv h)
   | MemReadInstr(p,v1,v2,i) ->
      L1_ast.MemReadInstr(p, compile_var v1 h, compile_var v2 h, i)
   | MemWriteInstr(p,v,i,sv) ->
      L1_ast.MemWriteInstr(p, compile_var v h, i, compile_sval sv h)
   | PlusInstr(p,v,tv) ->
      L1_ast.PlusInstr(p, compile_var v h, compile_tval tv h)
   | MinusInstr(p,v,tv) ->
      L1_ast.MinusInstr(p, compile_var v h, compile_tval tv h)
   | TimesInstr(p,v,tv) ->
      L1_ast.TimesInstr(p, compile_var v h, compile_tval tv h)
   | BitAndInstr(p,v,tv) ->
      L1_ast.BitAndInstr(p, compile_var v h, compile_tval tv h)
   | SllInstr(p,v,svr) ->
      L1_ast.SllInstr(p, compile_var v h, compile_svar svr h)
   | SrlInstr(p,v,svr) ->
      L1_ast.SrlInstr(p, compile_var v h, compile_svar svr h)
   | LtInstr(p,v,tv1,tv2) ->
      (* TODO XXX - the get_creg function throws a parse error on failure - is that okay? *)
      L1_ast.LtInstr(p, L1_ast.get_creg (compile_var v h), compile_tval tv1 h, compile_tval tv2 h)
   | LeqInstr(p,v,tv1,tv2) ->
      L1_ast.LeqInstr(p, L1_ast.get_creg (compile_var v h), compile_tval tv1 h, compile_tval tv2 h)
   | EqInstr(p,v,tv1,tv2) ->
      L1_ast.EqInstr(p, L1_ast.get_creg (compile_var v h), compile_tval tv1 h, compile_tval tv2 h)
   | LabelInstr(p,s) ->
      L1_ast.LabelInstr(p,s);
   | GotoInstr(p,s) ->
      L1_ast.GotoInstr(p,s);
   | LtJumpInstr(p,tv1,tv2,s1,s2) ->
      L1_ast.LtJumpInstr(p, compile_tval tv1 h, compile_tval tv2 h, s1, s2)
   | LeqJumpInstr(p,tv1,tv2,s1,s2) ->
      L1_ast.LeqJumpInstr(p, compile_tval tv1 h, compile_tval tv2 h, s1, s2)
   | EqJumpInstr(p,tv1,tv2,s1,s2) ->
      L1_ast.EqJumpInstr(p, compile_tval tv1 h, compile_tval tv2 h, s1, s2)
   | CallInstr(p,uv) ->
      L1_ast.CallInstr(p, compile_uval uv h)
   | TailCallInstr(p,uv) ->
      L1_ast.TailCallInstr(p, compile_uval uv h)
   | ReturnInstr(p) ->
      L1_ast.ReturnInstr(p);
   | PrintInstr(p,tv) ->
      L1_ast.PrintInstr(p, compile_tval tv h)
   | AllocInstr(p,tv1,tv2) ->
      L1_ast.AllocInstr(p, compile_tval tv1 h, compile_tval tv2 h)
   | ArrayErrorInstr(p,tv1,tv2) ->
      L1_ast.ArrayErrorInstr(p, compile_tval tv1 h, compile_tval tv2 h)

(* compiles an L2 sval into an L1 sval. the hashtable
 * has the variable register assignments *)
and compile_sval (sv : sval) (h : (int,L1_ast.reg) Hashtbl.t) : L1_ast.sval =
   match sv with
   | VarSVal(p,v) -> L1_ast.RegSVal(p, compile_var v h)
   | IntSVal(p,i) -> L1_ast.IntSVal(p,i)
   | LabelSVal(p,s) -> L1_ast.LabelSVal(p,s)

(* compiles an L2 uval into an L1 uval. the hashtable
 * has the variable register assignments *)
and compile_uval (uv : uval) (h : (int,L1_ast.reg) Hashtbl.t) : L1_ast.uval =
   match uv with
   | VarUVal(p,v) -> L1_ast.RegUVal(p, compile_var v h)
   | IntUVal(p,i) -> L1_ast.IntUVal(p,i)
   | LabelUVal(p,s) -> L1_ast.LabelUVal(p,s)

(* compiles an L2 tval into an L1 tval. the hashtable
 * has the variable register assignments *)
and compile_tval (tv : tval) (h : (int,L1_ast.reg) Hashtbl.t) : L1_ast.tval =
   match tv with
   | VarTVal(p,v) -> L1_ast.RegTVal(p, compile_var v h)
   | IntTVal(p,i) -> L1_ast.IntTVal(p,i)
   | LabelTVal(p,s) -> L1_ast.LabelTVal(p,s)

(* compiles an L2 var into an L1 reg. the hashtable
 * has the variable register assignments *)
and compile_var (v : var) (h : (int,L1_ast.reg) Hashtbl.t) : L1_ast.reg =
   match v with
   | VarOrReg(p,s,_) -> (
      if s == esi_id then L1_ast.EsiReg(p)
      else if s == edi_id then L1_ast.EdiReg(p)
      else if s == ebp_id then L1_ast.EbpReg(p)
      else if s == esp_id then L1_ast.EspReg(p)
      else if s == eax_id then L1_ast.CallerSaveReg(p,L1_ast.EaxReg(p))
      else if s == ecx_id then L1_ast.CallerSaveReg(p,L1_ast.EcxReg(p))
      else if s == edx_id then L1_ast.CallerSaveReg(p,L1_ast.EdxReg(p))
      else if s == ebx_id then L1_ast.CallerSaveReg(p,L1_ast.EbxReg(p))
      (* print_string ("compile_var: "^s^"\n"); *)
      else Hashtbl.find h s )

(* compiles an L2 svar into an L1 sreg. the hashtable
 * has the variable register assignments *)
and compile_svar (sv : svar) (h : (int,L1_ast.reg) Hashtbl.t) : L1_ast.sreg =
   match sv with
   | IntShVal(p,i) -> L1_ast.IntShVal(p,i)
   | ShVar(p,v) -> L1_ast.EcxShReg(p)  (* TODO XXX - make sure v really matches ecx? *)
;;
