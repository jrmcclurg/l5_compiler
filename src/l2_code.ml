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
 * In progress. Currently only has the "spill", "liveness",
 * and "graph" functions.
 *)

open L2_ast;;
open Utils;;

(*********************************************************
 **  LIVENESS                                           **
 *********************************************************)

(* prints a list of vars *)
let print_var_list (vl : var list) = 
      List.iter (fun v -> print_var v; print_string " ") vl;
      print_string "\n"
;;

(* compares two variables (returns 0 iff they are equal) *)
let compare_var (v1 : var) (v2 : var) : int =
  String.compare (get_var_name v1) (get_var_name v2)
;;

(* searches a list for a given var *)
let rec list_contains (vl : var list) (v : var) : bool =
   match vl with
   | [] -> false
   | t::ts ->
      if (compare_var t v) = 0 then true else list_contains ts v
;;

(* sorts a var list *)
let sort_vars (vl : var list) : var list =
  List.sort compare_var vl
;;
      
(* compares two var lists (returns true iff equal) *)
let rec compare_lists (vl1 : var list) (vl2 : var list) : bool =
   match (vl1,vl2) with
   | ([],[]) -> true
   | ([],_) -> false
   | (_,[]) -> false
   | (a::ax,b::bx) -> ((compare_var a b) = 0) && (compare_lists ax bx)
;;

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
let rec find_target_ins_helper (il : (instr * var list * var list) list) (s1 : string) (s2o : string option) : (var list) =
   match il with
   | [] -> []
   | (i1,ins,_)::is ->
      let l = (match (i1,s2o) with
      | (LabelInstr(_,s),None) -> if (s1 = s) then ins else []
      | (LabelInstr(_,s),Some(s2)) -> if ((s1 = s) || (s2 = s)) then ins else []
      | _ -> []) in
      (* go through the ins for the first instruction *)
      List.fold_right (fun i res -> 
         (* if the var i is not in the result list, add it *)
         if (not (list_contains res i)) then i::res else res
      ) l (find_target_ins_helper is s1 s2o)

(* gets the "ins" for a specified target label (see the find_target_ins_helper function)
 * (resulting list is SORTED) *)
and find_target_ins (il : (instr * var list * var list) list) (s1 : string) (s2o : string option) : (var list) =
   let l = find_target_ins_helper il s1 s2o in
   sort_vars l
;;

(* adds a var to the list, and sorts the resulting list *)
let add_and_sort (vl : var list) (v : var) = 
   let r = if (not (list_contains vl v)) then v::vl else vl in
   sort_vars r
;;

(* given instruction i, returns (gens, kills) *)
let get_gens_kills (i : instr) : (var list * var list) =
   match i with
   (* assignment *)
   | AssignInstr(_,v,VarSVal(_,v2)) -> ([v2], [v])
   | AssignInstr(_,v,_) -> ([], [v])
   (* mem read *)
   | MemReadInstr(_,v1,v2,_) -> ([v2],[v1])
   (* mem write *)
   | MemWriteInstr(_,v1,_,VarSVal(_,v2)) -> (add_and_sort [v1] v2,[])
   | MemWriteInstr(_,v1,_,_) -> ([v1],[])
   (* plus *)
   | PlusInstr(_,v,VarTVal(_,v2)) -> (add_and_sort [v] v2,[v])
   | PlusInstr(_,v,_) -> ([v], [v])
   (* minus *)
   | MinusInstr(_,v,VarTVal(_,v2)) -> (add_and_sort [v] v2,[v])
   | MinusInstr(_,v,_) -> ([v], [v])
   (* times *)
   | TimesInstr(_,v,VarTVal(_,v2)) -> (add_and_sort [v] v2,[v])
   | TimesInstr(_,v,_) -> ([v], [v])
   (* bitwise and *)
   | BitAndInstr(_,v,VarTVal(_,v2)) -> (add_and_sort [v] v2,[v])
   | BitAndInstr(_,v,_) -> ([v], [v])
   (* shift left *)
   | SllInstr(_,v,ShVar(_,v2)) -> (add_and_sort [v] v2,[v])
   | SllInstr(_,v,_) -> ([v], [v])
   (* shift right *)
   | SrlInstr(_,v,ShVar(_,v2)) -> (add_and_sort [v] v2,[v])
   | SrlInstr(_,v,_) -> ([v], [v])
   (* less-than comparison *)
   | LtInstr(_,v,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[v])
   | LtInstr(_,v,_,VarTVal(_,v3)) -> ([v3],[v])
   | LtInstr(_,v,VarTVal(_,v2),_) -> ([v2],[v])
   | LtInstr(_,v,_,_) -> ([], [v])
   (* less-than-or-equal-to comparison *)
   | LeqInstr(_,v,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[v])
   | LeqInstr(_,v,_,VarTVal(_,v3)) -> ([v3],[v])
   | LeqInstr(_,v,VarTVal(_,v2),_) -> ([v2],[v])
   | LeqInstr(_,v,_,_) -> ([], [v])
   (* equal-to comparison *)
   | EqInstr(_,v,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[v])
   | EqInstr(_,v,_,VarTVal(_,v3)) -> ([v3],[v])
   | EqInstr(_,v,VarTVal(_,v2),_) -> ([v2],[v])
   | EqInstr(_,v,_,_) -> ([], [v])
   (* label *)
   | LabelInstr(_,_) -> ([],[])
   (* goto *)
   | GotoInstr(_,_) -> ([],[])
   (* less-than jump *)
   | LtJumpInstr(_,VarTVal(_,v1),VarTVal(_,v2),_,_) -> (add_and_sort [v1] v2,[])
   | LtJumpInstr(_,_,VarTVal(_,v2),_,_) -> ([v2],[])
   | LtJumpInstr(_,VarTVal(_,v1),_,_,_) -> ([v1],[])
   (* less-than-or-equal-to jump *)
   | LeqJumpInstr(_,VarTVal(_,v1),VarTVal(_,v2),_,_) -> (add_and_sort [v1] v2,[])
   | LeqJumpInstr(_,_,VarTVal(_,v2),_,_) -> ([v2],[])
   | LeqJumpInstr(_,VarTVal(_,v1),_,_,_) -> ([v1],[])
   (* equal-to jump *)
   | EqJumpInstr(_,VarTVal(_,v1),VarTVal(_,v2),_,_) -> (add_and_sort [v1] v2,[])
   | EqJumpInstr(_,_,VarTVal(_,v2),_,_) -> ([v2],[])
   | EqJumpInstr(_,VarTVal(_,v1),_,_,_) -> ([v1],[])
   (* call *)
   | CallInstr(_,VarUVal(p,v)) ->
      let l = add_and_sort [EaxReg(p);EdxReg(p);EcxReg(p)] v in
      (l,[EaxReg(p);EbxReg(p);EcxReg(p);EdxReg(p)])
   | CallInstr(p,_) -> ([EaxReg(p);EcxReg(p);EdxReg(p)],[EaxReg(p);EbxReg(p);EcxReg(p);EdxReg(p)])
   (* tail-call *)
   | TailCallInstr(_,VarUVal(p,v)) ->
      let l = add_and_sort [EaxReg(p);EdxReg(p);EcxReg(p);EdiReg(p);EsiReg(p)] v in
      (l,[])
   | TailCallInstr(p,_) -> ([EaxReg(p);EcxReg(p);EdiReg(p);EdxReg(p);EsiReg(p)],[])
   (* return *)
   | ReturnInstr(p) -> ([EaxReg(p);EdiReg(p);EsiReg(p)],[])
   (* print *)
   | PrintInstr(p,VarTVal(_,v)) -> ([v],[EaxReg(p);EcxReg(p);EdxReg(p)])
   | PrintInstr(p,_) -> ([],[EaxReg(p);EcxReg(p);EdxReg(p)])
   (* allocate *)
   | AllocInstr(p,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[EaxReg(p);EcxReg(p);EdxReg(p)])
   | AllocInstr(p,_,VarTVal(_,v3)) -> ([v3],[EaxReg(p);EcxReg(p);EdxReg(p)])
   | AllocInstr(p,VarTVal(_,v2),_) -> ([v2],[EaxReg(p);EcxReg(p);EdxReg(p)])
   | AllocInstr(p,_,_) -> ([],[EaxReg(p);EcxReg(p);EdxReg(p)])
   (* array-error *)
   | ArrayErrorInstr(p,VarTVal(_,v2),VarTVal(_,v3)) -> (add_and_sort [v2] v3,[EaxReg(p);EcxReg(p);EdxReg(p)])
   | ArrayErrorInstr(p,_,VarTVal(_,v3)) -> ([v3],[EaxReg(p);EcxReg(p);EdxReg(p)])
   | ArrayErrorInstr(p,VarTVal(_,v2),_) -> ([v2],[EaxReg(p);EcxReg(p);EdxReg(p)])
   | ArrayErrorInstr(p,_,_) -> ([],[EaxReg(p);EcxReg(p);EdxReg(p)])
   | _ -> ([],[])
;;

(*
 * compute_ins gens kills outs
 *
 * Computes the "ins" using the formula
 * ins = gens U (outs - kills)
 * (where "U" is set union)
 * The result is sorted
 *)
let compute_ins (gens : var list) (kills : var list) (outs : var list) : var list =
   let result = List.fold_right (fun o l ->
      (* find the ones that are in "outs", but not in "kills" *)
      if ((not (list_contains kills o)) && (not (list_contains l o))) then o::l else l
   ) outs gens in (* the initial value "gens" here gets added to (outs - kills),
                   * which is computed during the fold operation *)
   sort_vars result (* sort the result *)
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
let rec liveness_helper (il : (instr * var list * var list) list) :
                                        ((instr * var list * var list) list) =
   (* go through the instructions *)
   let (_,result,change) = List.fold_right (fun (i,ins,outs) (prev_ins,res,flag) -> 
      (* get the gens and kills for this instruction *)
      let (gens,kills) = get_gens_kills i in
      (* compute the new "ins" list *)
      let new_ins = compute_ins gens kills outs in
      (* compute the new "outs" list as the union of the "ins" of
       * the successor instruction(s) *)
      let new_outs = (match i with
      (* if we're looking at a branch instruction, find the ins for the target *)
      | GotoInstr(_,s) -> find_target_ins il s None
      | LtJumpInstr(_,_,_,s1,s2) -> find_target_ins il s1 (Some(s2))
      | LeqJumpInstr(_,_,_,s1,s2) -> find_target_ins il s1 (Some(s2))
      | EqJumpInstr(_,_,_,s1,s2) -> find_target_ins il s1 (Some(s2))
      | ReturnInstr(_) -> []
      | TailCallInstr(_,_) -> []
      | ArrayErrorInstr(_,_,_) -> []
      (* prev_ins is maintained as the successor instrution's "ins" list *)
      | _ -> prev_ins) in
      (* compare new_ins with ins and new_outs with outs to determine if anything changed *)
      (ins,(i,new_ins,new_outs)::res,flag || (not (compare_lists ins new_ins))
                                          || (not (compare_lists outs new_outs)))
   ) il ([],[],false) in
   (* if the "ins" or "outs" changed, process again, otherwise we're done *)
   if change then liveness_helper result else result
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
let liveness (il : instr list) : ((var list) list * (var list) list) = 
   (* add an empty "in" and "out" list for each instruction *)
   let nl = List.map (fun i -> (i,[],[])) il in
   (* get the ins and outs (this is a fixpoint operator *)
   let l = liveness_helper nl in
   (* return the ins and outs in the appropriate format *)
   List.fold_right (fun (i,ins,outs) (inl,outl) -> (ins::inl,outs::outl)) l ([],[])
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
let add_edge (v1 : var) (v2o : var option)
                  (h : (string, (var * (string,var) Hashtbl.t)) Hashtbl.t) : unit =
   (* leave ebp/esp registers out of the graph *)
   match v1 with
   | EbpReg(_) -> ()
   | EspReg(_) -> ()
   (* process registers other than ebp/esp... *)
   | _ -> (
   (* get the name of v1 *)
   let name = (get_var_name v1) in
   let (_,t) = (
      (* see if there's a source vertex for "name" in the graph
       * (if there is, "t" will be bound to its table
       * of destinations) *)
      try Hashtbl.find h name
      with _ ->
         (* if there's no source vertex "name" in the graph, add one,
          * along with an empty table for destination vertices *)
         let t2 = ((Hashtbl.create 10) : (string,var) Hashtbl.t) in
         Hashtbl.replace h name (v1,t2);
         (v1,t2)
   ) in (
   match v2o with
   (* ignore v2o if it is ebp/esp *)
   | Some(EbpReg(_)) -> ()
   | Some(EspReg(_)) -> ()
   (* otherwise, if v2o okay... *)
   | Some(v2) ->
      (* get the name of v2 *)
      let name2 = (get_var_name v2) in
      (* if v2 is a different variable/register than v1, add
       * an edge (v1,v2) by putting v2 in v1's dest table *)
      if (name <> name2) then Hashtbl.replace t (get_var_name v2) v2
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
let add_all_edges (vl1 : var list) (vl2 : var list) (so : (var * var) option)
                  (h : (string, (var * (string,var) Hashtbl.t)) Hashtbl.t) : unit =
   (* if vl1 is empty, just add a vertex for each item in vl2 *)
   match vl1 with
   | [] -> List.iter (fun v2 -> add_edge v2 None h) vl2
   | _ ->
   (* if vl1 is non-empty, iterate through its items *)
   List.iter (fun v1 ->
      (match vl2 with
      (* if vl2 is empty, just add a vertex for the current item of vl1 *)
      | [] -> add_edge v1 None h
      | _ ->
         (* if vl2 is non-empty, iterate through its item *)
         List.iter (fun v2 ->
            (* get the names for v1/v2 *)
            let s1 = get_var_name v1 in
            let s2 = get_var_name v2 in
            (match so with
            (* if there's an edge we want to ignore... *)
            | Some(v1t,v2t) ->
               let s1t = get_var_name v1t in
               let s2t = get_var_name v2t in
               (* if (v1,v2) matches the ignored edge, then
                * just add disconnected vertices v1 and v2 *)
               if (((s1=s1t) && (s2=s2t)) || ((s1=s2t) && (s2=s1t))) then (
                  add_edge v1 None h;
                  add_edge v2 None h
               )
               (* if (v1,v2) is not the ignored edge... *)
               else (
                  (* add the edges (v1,v2) and (v2,v1) *)
                  add_edge v1 (Some(v2)) h;
                  add_edge v2 (Some(v1)) h )
            (* if there's no edge we want to ignore... *)
            | _ -> 
               (* add the edges (v1,v2) and (v2,v1) *)
               add_edge v1 (Some(v2)) h;
               add_edge v2 (Some(v1)) h )
         ) vl2 )
   ) vl1
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
let rec compute_adjacency_table (il : (instr * var list * var list) list)
                                (h : (string, (var * (string,var) Hashtbl.t)) Hashtbl.t)
                                (first : bool) : unit =
   match (il) with
   | [] -> ()
   | (i,ins,outs)::more -> 
      (* "temp" is a potential edge to ignore when generating the graph *)
      let temp = (match i with
      (* if this instruction is a <- b, then a,b don't conflict, so
       * we want to ignore the edge (a,b) in the graph *)
      | AssignInstr(_,v1,VarSVal(_,v2)) -> Some((v1,v2))
      (* for any other instructions, we don't ignore the edge *)
      | _ -> None ) in
      (* add edges between variables that are live at the same time
       * (this means any variables that appear in any "out" set together,
       * or any variables that appear together in the first instruction's
       * "in" set *)
      if first then add_all_edges ins ins None h else add_all_edges ins [] None h;
      add_all_edges outs outs temp h;
      (* add edges between the kills and the out set *)
      let (gens,kills) = get_gens_kills i in
      (* NOTE: we don't need to add vertices for the gens, since all the gens
       * except for that of the first instruction go into the outs of previous
       * instructions.  The gens for the first instruction are capture by the ins
       * of the first instruction. *)
      add_all_edges kills outs temp h;
      (* handle the special instructions *)
      (* l1 is all the usable registers except ecx *)
      let l1 = [EaxReg(NoPos);EbxReg(NoPos);EdiReg(NoPos);EdxReg(NoPos);EsiReg(NoPos)] in
      (* l2 is the callee-save registers *)
      let l2 = [EdiReg(NoPos);EsiReg(NoPos)] in
      (match i with
      (* any shift variable v will conflict with all usable registers except ecx
       * (since ecx is the only allowable shift register in the x86 instruction) *)
      | SllInstr(_,_,ShVar(_,(Var(_,_) as v))) -> add_all_edges [v] l1 None h
      | SrlInstr(_,_,ShVar(_,(Var(_,_) as v))) -> add_all_edges [v] l1 None h
      (* a destination variable for comparisons will conflict with the 
       * callee-save registers, since the callER-save registers are the only
       * valid destinations *)
      | LtInstr(_,(Var(_,_) as v),_,_) -> add_all_edges [v] l2 None h
      | LeqInstr(_,(Var(_,_) as v),_,_) -> add_all_edges [v] l2 None h
      | EqInstr(_,(Var(_,_) as v),_,_) -> add_all_edges [v] l2 None h
      | _ -> ());
      (* recursively process the remaining instructions *)
      compute_adjacency_table more h false
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
let graph_color (il : instr list) : ((var list) list * (var * var) list * bool) =
   (* perform the liveness analysis based on the instruction list *)
   let nl = List.map (fun i -> (i,[],[])) il in
   let il2 = liveness_helper nl in
   (* make sure all of the usable registers are connected *)
   let l1 = [EaxReg(NoPos);EbxReg(NoPos);EcxReg(NoPos);EdiReg(NoPos);EdxReg(NoPos);EsiReg(NoPos)] in
   (* create an empty hashtable for the graph *)
   let h = ((Hashtbl.create (List.length l1)) : (string, (var * (string,var) Hashtbl.t)) Hashtbl.t) in
   (* add edges between all the usable registers *)
   add_all_edges l1 l1 None h;
   (* populate h with the conflict graph *)
   compute_adjacency_table il2 h true;
   (* find all the source vertices in graph h *)
   let keys = Hashtbl.fold (fun k (v,_) res -> 
      k::res
   ) h [] in
   (* sort the source vertices by name *)
   let keys2 = List.sort String.compare keys in
   (* now we do the heuristic graph coloring *)
   (* create a hashtable for mapping variable names to their register (color) assignments *)
   let assignments = ((Hashtbl.create (List.length l1)) : (string,var) Hashtbl.t) in
   (* go through the graph (via the sorted keys2 list)
    * and compute the return values (ag,colors,ok) *)
   let (ag,colors,ok) = List.fold_left (fun (r2,r3,flag) x -> 
      (* find the current source variable "x" in the graph
       * (v is the corresponding var data structure, and 
       * tb is the hashtable of destinations) *)
      let (v,tb) = Hashtbl.find h x in
      (* get the list of destination variables *)
      let tbl = Hashtbl.fold (fun _ vr res2 ->
         vr::res2
      ) tb [] in
      (* go through all of the usable registers l1, 
       * and compute an optional color (register)
       * assignment l2 *)
      let l2 = List.fold_left (fun r l3 ->
         (* the_name is the current register name *)
         let the_name = (get_var_name l3) in
         (* check if "r" already contains a coloring *)
         match r with
         (* if "r" does not contain a coloring yet... *)
         | None ->
            (* go through the list tbl of destination vertices to see
             * if register the_name is contained there *)
            let found = (List.fold_left (fun flag t ->
               let f = 
               (match t with
               (* if this destination vertex is a variable... *)
               | Var(_,s) ->
                  (* look it up in the assigned reg table *)
                  (try let test = Hashtbl.find assignments s in ((get_var_name test)=the_name)
                  with _ -> false)
               (* if this destination vertex is a register... *)
               | _ -> if ((get_var_name t)=the_name) then true else false) in
               (flag || f)
            ) false tbl) in
            (* if register the_name was found in the dest list,
             * we can't used it as the coloring assignment *)
            if found then None
            (* otherwise, if the_name was NOT found, we can use
             * it as a coloring assignment (and add it to the
             * table of assignments) *)
            else (
               Hashtbl.add assignments x l3;
               (Some(l3))
            )
         (* if "r" already contains a coloring, just use that one *)
         | Some(_) -> r
      ) None l1 in

      (* based on the current source vertex v, compute newl,
       * the updated list of coloring assignments, and
       * f, the updated status of the coloring (true iff successful
       * coloring) *)
      let (newl,f) = (match v with
      (* if the current source vertex is a variable... *)
      | Var(_,_) ->
         (* if we found a valid coloring for v, update the list of
          * coloring assignments *)
         (match l2 with
         | Some(c) -> (r3@[(v,c)],true) 
         | _ -> (r3,false) )
      (* if the current source vertex is a REGISTER, we don't need
       * to add a register assignment *)
      | _ -> (r3,true)) in
      (* add the row (v,dest1,dest2,dest3,...) to the adjacency
       * table, where [dest1;dest2;dest] is the sorted version of
       * destination list tbl.  also update the coloring assignment
       * list (newl) and the result status (f && flag) which is
       * true iff ALL source vertices are able to be assigned a
       * color properly *)
      (r2@[(v::(sort_vars tbl))],newl,f && flag)
   ) ([],[],true) keys2 in
   (ag,colors,ok)
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

(*********************************************************
 **  L2-to-L1 CODE GENERATION                           **
 *********************************************************)

let rec compile_program (p : L2_ast.program) : L1_ast.program =
   match p with
   | Program(p,fl) -> 
      let fl2 = List.map (fun f -> compile_func f) fl in
      L1_ast.Program(p, fl2)

and compile_func (f : L2_ast.func) : L1_ast.func = 
   match f with
   | Function(p,so,il) -> 
   let first = (match so with
   | None -> true
   | _ -> false) in
   let save    = [AssignInstr(p,Var(p,"<edi>"),VarSVal(p,EdiReg(p)));
                  AssignInstr(p,Var(p,"<esi>"),VarSVal(p,EsiReg(p)))] in
   let restore = [AssignInstr(p,EdiReg(p),VarSVal(p,Var(p,"<edi>")));
                  AssignInstr(p,EsiReg(p),VarSVal(p,Var(p,"<esi>")))] in
   (* add save to the front of list, and restore before each tail-call and return *)
   let il2 = List.fold_left (fun res i ->
      match (so,i) with
      | (None,_) -> res @ [i]
      | (_,TailCallInstr(_,_)) -> res @ restore @ [i]
      | (_,ReturnInstr(_)) -> res @ restore @ [i]
      | _ -> res @ [i]
   ) (if first then [] else save) il in
   let (il3,num_spilled) = compile_instr_list il2 0L in
   let il4 = if ((num_spilled > 0L) && (not first)) then
      (L1_ast.MinusInstr(p,L1_ast.EspReg(p),L1_ast.IntTVal(p, (Int64.mul (-4L) num_spilled))))::il3
   else il3 in
   L1_ast.Function(p,so,il4)

(* this is a fixpoint operator where i is the current number of spilled vars *)
and compile_instr_list (il : L2_ast.instr list) (num : int64) : (L1_ast.instr list * int64) =
   let (at,colors,ok) = graph_color il in
   (* if the graph coloring failed... *)
   if (not ok) then (
      (* just pick any old variable to spill *)
      let nameop = List.fold_left (fun res vl -> 
         match (List.hd vl) with
	 | Var(_,s) -> Some(s)
	 | _ -> res
      ) None at in
      (* TODO spill and try again *)
      match nameop with
      | None -> parse_error "register allocation failed" (* TODO don't use parse_error for this message *)
      | Some(name) ->
         let il2 = spill il name (Int64.mul (-4L) (Int64.add num (1L))) "<s>" in
         compile_instr_list il2 (Int64.add num (1L))
   )
   (* if the graph coloring succeeded *)
   else (
      (* set up the replacement table *)
      let h = ((Hashtbl.create (List.length colors)) : (string,L1_ast.reg) Hashtbl.t) in
      List.iter (fun (v,c) -> 
         let name = get_var_name v in
         let r = (match c with
	 | EsiReg(p) -> L1_ast.EsiReg(p)
	 | EdiReg(p) -> L1_ast.EdiReg(p)
	 | EbpReg(p) -> L1_ast.EbpReg(p)
	 | EspReg(p) -> L1_ast.EspReg(p)
	 | EaxReg(p) -> L1_ast.CallerSaveReg(p,L1_ast.EaxReg(p))
	 | EcxReg(p) -> L1_ast.CallerSaveReg(p,L1_ast.EcxReg(p))
	 | EdxReg(p) -> L1_ast.CallerSaveReg(p,L1_ast.EdxReg(p))
	 | EbxReg(p) -> L1_ast.CallerSaveReg(p,L1_ast.EbxReg(p))
	 | Var(p,_) -> die_error p "invalid register coloring" (* TODO this should never happen *)
	 ) in
	 Hashtbl.replace h name r
      ) colors;
      (List.map (fun i -> compile_instr i h) il, num)
   )

and compile_instr (i : instr) (h : (string,L1_ast.reg) Hashtbl.t) : L1_ast.instr =
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

and compile_sval (sv : sval) (h : (string,L1_ast.reg) Hashtbl.t) : L1_ast.sval =
   match sv with
   | VarSVal(p,v) -> L1_ast.RegSVal(p, compile_var v h)
   | IntSVal(p,i) -> L1_ast.IntSVal(p,i)
   | LabelSVal(p,s) -> L1_ast.LabelSVal(p,s)

and compile_uval (uv : uval) (h : (string,L1_ast.reg) Hashtbl.t) : L1_ast.uval =
   match uv with
   | VarUVal(p,v) -> L1_ast.RegUVal(p, compile_var v h)
   | IntUVal(p,i) -> L1_ast.IntUVal(p,i)
   | LabelUVal(p,s) -> L1_ast.LabelUVal(p,s)

and compile_tval (tv : tval) (h : (string,L1_ast.reg) Hashtbl.t) : L1_ast.tval =
   match tv with
   | VarTVal(p,v) -> L1_ast.RegTVal(p, compile_var v h)
   | IntTVal(p,i) -> L1_ast.IntTVal(p,i)
   | LabelTVal(p,s) -> L1_ast.LabelTVal(p,s)

and compile_var (v : var) (h : (string,L1_ast.reg) Hashtbl.t) : L1_ast.reg =
   match v with
   | EsiReg(p) -> L1_ast.EsiReg(p)
   | EdiReg(p) -> L1_ast.EdiReg(p)
   | EbpReg(p) -> L1_ast.EbpReg(p)
   | EspReg(p) -> L1_ast.EspReg(p)
   | EaxReg(p) -> L1_ast.CallerSaveReg(p,L1_ast.EaxReg(p))
   | EcxReg(p) -> L1_ast.CallerSaveReg(p,L1_ast.EcxReg(p))
   | EdxReg(p) -> L1_ast.CallerSaveReg(p,L1_ast.EdxReg(p))
   | EbxReg(p) -> L1_ast.CallerSaveReg(p,L1_ast.EbxReg(p))
   | Var(p,s) ->
      (* print_string ("compile_var: "^s^"\n"); *)
      Hashtbl.find h s

and compile_svar (sv : svar) (h : (string,L1_ast.reg) Hashtbl.t) : L1_ast.sreg =
   match sv with
   | IntShVal(p,i) -> L1_ast.IntShVal(p,i)
   | ShVar(p,v) -> L1_ast.EcxShReg(p)  (* TODO XXX - make sure v really matches ecx? *)
;;
