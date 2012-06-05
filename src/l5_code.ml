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
open Flags;;

(*********************************************************
 **  L5-to-L4 CODE GENERATION                           **
 *********************************************************)

let fv_id = add_symbol "fv";;
let bv_id = add_symbol "bv";;

let fast_prefix = "FAST";;

let rec make_var_list (p : pos) (prefix : string) (n : int) : L4_ast.var list =
   let name = (prefix^(string_of_int n)) in
   if n = 0 then []
   else if n = 1 then [L4_ast.Var(p,add_symbol name)]
   else (
      (make_var_list p prefix (n-1))@[L4_ast.Var(p,add_symbol name)]
   )
;;

let get_func (p : pos) (nm : string) (num : int) (fn : ((int * int) option) ref) :
(int * int * L4_ast.var list * L4_ast.var list * L4_ast.var option) =
   match !fn with
   | None ->
      let name = get_unique_symbol (l5_prefix^nm) in
      let fname = get_unique_symbol (l5_prefix^fast_prefix^nm) in
      fn := Some(name,fname);
      let fv = L4_ast.Var(p,fv_id) in
      let bv = L4_ast.Var(p,bv_id) in
      let fvars = make_var_list p "p" num in 
      (name,fname,[fv;bv],fvars,Some(bv))
   | Some(s1,s2) -> (s1,s2,[],[],None)
;;

let plus_func_name = ref (None : (int * int) option);;
let get_plus_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "plus" 2 plus_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.PlusExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.PlusExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let minus_func_name = ref (None : (int * int) option);;
let get_minus_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "minus" 2 minus_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.MinusExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.MinusExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let times_func_name = ref (None : (int * int) option);;
let get_times_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "times" 2 times_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.TimesExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.TimesExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let lt_func_name = ref (None : (int * int) option);;
let get_lt_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "lt" 2 lt_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.LtExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.LtExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let leq_func_name = ref (None : (int * int) option);;
let get_leq_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "leq" 2 leq_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.LeqExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.LeqExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let eq_func_name = ref (None : (int * int) option);;
let get_eq_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "eq" 2 eq_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.EqExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.EqExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let numberq_func_name = ref (None : (int * int) option);;
let get_numberq_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "numberq" 1 numberq_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.NumberPredExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.NumberPredExp(p,L4_ast.VarExp(p,List.nth fvars 0)))
            ])
   | _ -> (name,fname,[])
;;

let arrayq_func_name = ref (None : (int * int) option);;
let get_arrayq_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "arrayq" 1 arrayq_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.ArrayPredExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.ArrayPredExp(p,L4_ast.VarExp(p,List.nth fvars 0)))
            ])
   | _ -> (name,fname,[])
;;

let print_func_name = ref (None : (int * int) option);;
let get_print_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "print" 1 print_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.PrintExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.PrintExp(p,L4_ast.VarExp(p,List.nth fvars 0)))
            ])
   | _ -> (name,fname,[])
;;

let newarr_func_name = ref (None : (int * int) option);;
let get_newarr_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "newarr" 2 newarr_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.NewArrayExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.NewArrayExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let aref_func_name = ref (None : (int * int) option);;
let get_aref_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "aref" 2 aref_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.ArefExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.ArefExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let aset_func_name = ref (None : (int * int) option);;
let get_aset_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "aset" 3 aset_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.AsetExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1l)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,2l)),true));
             L4_ast.Function(p,fname,fvars,
             L4_ast.AsetExp(p,L4_ast.VarExp(p,List.nth fvars 0),
                              L4_ast.VarExp(p,List.nth fvars 1),
                              L4_ast.VarExp(p,List.nth fvars 2),true))
            ])
   | _ -> (name,fname,[])
;;

let alen_func_name = ref (None : (int * int) option);;
let get_alen_func (p : pos) : (int * int * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "alen" 1 alen_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.AlenExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0l))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.AlenExp(p,L4_ast.VarExp(p,List.nth fvars 0)))
            ])
   | _ -> (name,fname,[])
;;

let rec var_list_contains (vl : L5_ast.var list) (s : int) : bool =
   match vl with
   | []-> false
   | (Var(_,s2))::more -> ((s2 = s) || (var_list_contains more s))
;;

let print_var_list (vl : L5_ast.var list) = 
   print_string "[";
   List.iter (fun v -> print_var v; print_string " ") vl;
   print_string "]\n"
;;

let rec replace_in_exp (e : L5_ast.exp) (target : L5_ast.var) (repl : L5_ast.exp) : L5_ast.exp =
   let name = (match target with
     | Var(_,s) -> s) in
   let result = (match e with
      | LambdaExp(p,vl2,e2) ->
         if (var_list_contains vl2 name) then e
         else LambdaExp(p,vl2,replace_in_exp e2 target repl)
      | VarExp(p, Var(p2,s)) ->
         if (name = s) then repl else e
      | LetExp(p, (Var(p2,s) as v), e1, e2) ->
         LetExp(p,v,replace_in_exp e1 target repl,
                    (if (name = s) then e2 else replace_in_exp e2 target repl))
      | LetRecExp(p, (Var(p2,s) as v), e1, e2) ->
         LetRecExp(p,v,(if (name = s) then e1 else replace_in_exp e1 target repl),
                       (if (name = s) then e2 else replace_in_exp e2 target repl))
      | IfExp(p, e1, e2, e3) ->
         IfExp(p,replace_in_exp e1 target repl,
                 replace_in_exp e2 target repl,
                 replace_in_exp e3 target repl)
      | NewTupleExp(p,el) ->
         NewTupleExp(p,List.map (fun e -> replace_in_exp e target repl) el)
      | BeginExp(p,e1,e2) ->
         BeginExp(p,replace_in_exp e1 target repl,replace_in_exp e2 target repl)
      | AppExp(p,e,el) ->
         AppExp(p,replace_in_exp e target repl,
                  List.map (fun e -> replace_in_exp e target repl) el)
      | PrimExp(p, pr) -> e
      | IntExp(p, i) -> e ) in
   result
;;

let rec get_free_vars (e : L5_ast.exp) (vl : L5_ast.var list) : (L5_ast.var list) =
   (*print_string "Get free vars: ";
   print_exp e;
   print_string "\n";*)
   match e with
   | LambdaExp(_,vl2,e) -> get_free_vars e (vl@vl2)
   | VarExp(_, (Var(_,s) as v)) -> 
      if (var_list_contains vl s) then [] else [v]
   | LetExp(_, v, e1, e2) ->
      let l = (get_free_vars e1 vl) in (* NOTE: the "v" in LET doesn't shadow the e1, but in LETREC it does *)
      l@(get_free_vars e2 (v::(l@vl)))
   | LetRecExp(_, v, e1, e2) ->
      let l = (get_free_vars e1 (v::vl)) in
      l@(get_free_vars e2 (v::l@vl))
   | IfExp(_, e1, e2, e3) ->
      let l1 = get_free_vars e1 vl in
      let l2 = get_free_vars e2 (l1@vl) in
      let l3 = get_free_vars e3 (l1@l2@vl) in
      (l1@l2@l3)
   | NewTupleExp(_,el) ->
      let (ret,_) = List.fold_left (fun (l,vlx) e ->
         let l2 = get_free_vars e vlx in
         ((l2@l), (l2@vlx))
      ) ([],vl) el in
      ret
   | BeginExp(_,e1,e2) ->
      let l1 = get_free_vars e1 vl in
      let l2 = get_free_vars e2 (l1@vl) in
      l1@l2
   | AppExp(_,e,el) ->
      let l1 = get_free_vars e vl in
      let (ret,_) = List.fold_left (fun (l,vlx) e ->
         let l2 = get_free_vars e vlx in
         ((l2@l), (l2@vlx))
      ) (l1,(l1@vl)) el in
      ret
   | PrimExp(_, p) -> []
   | IntExp(_, i) -> []
;;

(*
 * These functions compile an L5 program into an L4 program
 *)

let rec compile_program (pr : L5_ast.program) : L4_ast.program =
   match pr with
   | Program(p,e) -> 
      let start_time = Sys.time () in
      if !debug_5 || !verbose_mode then (
         print_string ("Compiling L5 to L4..."^(if !verbose_mode then " " else "\n"));
         flush Pervasives.stdout
      );
      let (e2,fl) = compile_exp e in
      if !debug_5 || !verbose_mode then (
         let diff = (Sys.time ()) -. start_time in
         print_string ((if !verbose_mode then "" else "...")^"done"^
            (if !verbose_mode then "" else " with L5->L4")^": "^(string_of_float diff)^" sec.\n");
         flush Pervasives.stdout
      );
      L4_ast.Program(p,e2,fl)

and compile_exp (e : L5_ast.exp) : (L4_ast.exp * L4_ast.func list) =
   match e with
   | LambdaExp(p,vl,e) -> 
      (*print_string "PROCESSING LAMBDA: ";
      print_exp e;
      print_string "\n";*)
      let name = get_unique_symbol l5_prefix in
      let fparam = get_unique_symbol l5_prefix in
      let bparam = get_unique_symbol l5_prefix in
      let free_vars = (*[Var(p,"m1");Var(p,"m2")]*) get_free_vars e vl in
      let (e2,fl) = compile_exp e in
      let (e3,_) = List.fold_right (fun v (ex,k) ->
         (L4_ast.LetExp(p,compile_var v,L4_ast.ArefExp(p,L4_ast.VarExp(p,L4_ast.Var(p,bparam)),
                                           L4_ast.IntExp(p,Int32.of_int k)),ex), k-1)
      ) vl (e2,(List.length vl)-1) in
      let (e4,_) = List.fold_right (fun v (ex,k) ->
         (L4_ast.LetExp(p,compile_var v,L4_ast.ArefExp(p,L4_ast.VarExp(p,L4_ast.Var(p,fparam)),
                                           L4_ast.IntExp(p,Int32.of_int k)),ex), k-1)
      ) free_vars (e3,(List.length free_vars)-1) in
      (L4_ast.MakeClosureExp(p,name,
         L4_ast.NewTupleExp(p,List.map (fun f -> L4_ast.VarExp(p,compile_var f)) free_vars)),
       (L4_ast.Function(p,name,[L4_ast.Var(p,fparam);L4_ast.Var(p,bparam)],e4))::fl)
   | VarExp(p,v) -> (L4_ast.VarExp(p,compile_var v), [])
   | LetExp(p,v,e1,e2) ->
      let (e1n,fl1) = compile_exp e1 in
      let (e2n,fl2) = compile_exp e2 in
      (L4_ast.LetExp(p,compile_var v,e1n,e2n),fl1@fl2)
   | LetRecExp(p,v,e1,e2) ->
      (*print_string ("LETREC compiling ");
      print_exp e1;
      print_string ", ";
      print_exp e2;
      print_string "\n";*)
      let x = VarExp(p,v) in
      let zero = IntExp(p,0l) in
      let arf = AppExp(p,PrimExp(p,ArefPrim(p)),[x;zero]) in
      let e1_rep = replace_in_exp e1 v arf in
      let e2_rep = replace_in_exp e2 v arf in
      (*print_string "REPLACING: ";
      print_exp e1;
      print_string " -> ";
      print_exp e1_rep;
      print_string "\n";
      print_string "REPLACING: ";
      print_exp e2;
      print_string " -> ";
      print_exp e2_rep;
      print_string "\n";*)
      let v2 = compile_var v in
      let (e1n,fl1n) = compile_exp e1_rep in
      let (e2n,fl2n) = compile_exp e2_rep in
      let fl1 = fl1n in
      let fl2 = fl2n in
      (*let fl1 = List.map (fun (L4_ast.Function(p,s,vl,e)) ->
         let e2 = if L4_code.var_list_contains vl v2 then e
         else (
            print_string "REPLACE in";
            L4_ast.print_exp e;
            print_string ", ";
            L4_ast.print_var v2;
            print_string ", ";
            L4_ast.print_exp arf;
            print_string "\n";
            L4_code.replace_in_exp e v2 arf) in
         L4_ast.Function(p,s,vl,e2)
      ) fl1n in
      let fl2 = List.map (fun (L4_ast.Function(p,s,vl,e)) ->
         let e2 = if L4_code.var_list_contains vl v2 then e
         else (
            print_string "REPLACE in";
            L4_ast.print_exp e;
            print_string ", ";
            L4_ast.print_var v2;
            print_string ", ";
            L4_ast.print_exp arf;
            print_string "\n";
            L4_code.replace_in_exp e v2 arf) in
         L4_ast.Function(p,s,vl,e2)
      ) fl2n in*)
      let (zero2,_) = compile_exp zero in
      let (x2,_) = compile_exp x in
      (L4_ast.LetExp(p,v2,
         L4_ast.NewTupleExp(p,[zero2]),
         L4_ast.BeginExp(p,L4_ast.AsetExp(p,x2,zero2,e1n,true),e2n)),fl1@fl2)
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
      let (el2,fl2) = List.fold_left (fun (elx,flx) ex ->
         let (et,flt) = compile_exp ex in
         (elx@[et], flx@flt)
      ) ([],[]) el in
      (match e with
      (*| PrimExp(p,pr) ->
         let (ex,fl) = compile_prim pr false in
         (L4_ast.AppExp(p,ex,el2),fl@fl2)*)
      | PrimExp(p,pr) ->
         (match pr with
	 | PlusPrim(p2) ->
            if List.length el2 <> 2 then die_error p "the '+' operator takes two arguments";
            (L4_ast.PlusExp(p,List.nth el2 0,List.nth el2 1),fl2)
	 | MinusPrim(p2) ->
            if List.length el2 <> 2 then die_error p "the '-' operator takes 2 arguments";
            (L4_ast.MinusExp(p,List.nth el2 0,List.nth el2 1),fl2)
	 | TimesPrim(p2) ->
            if List.length el2 <> 2 then die_error p "the '*' operator takes 2 arguments";
            (L4_ast.TimesExp(p,List.nth el2 0,List.nth el2 1),fl2)
         | LtPrim(p2) ->
            if List.length el2 <> 2 then die_error p "the '<' operator takes 2 arguments";
            (L4_ast.LtExp(p,List.nth el2 0,List.nth el2 1),fl2)
         | LeqPrim(p2) ->
            if List.length el2 <> 2 then die_error p "the '<=' operator takes 2 arguments";
            (L4_ast.LeqExp(p,List.nth el2 0,List.nth el2 1),fl2)
         | EqPrim(p2) ->
            if List.length el2 <> 2 then die_error p "the '=' operator takes 2 arguments";
            (L4_ast.EqExp(p,List.nth el2 0,List.nth el2 1),fl2)
         | NumberPredPrim(p2) ->
            if List.length el2 <> 1 then die_error p "the 'number?' operator takes 1 argument";
            (L4_ast.NumberPredExp(p,List.nth el2 0),fl2)
         | ArrayPredPrim(p2) ->
            if List.length el2 <> 1 then die_error p "the 'array?' operator takes 1 argument";
            (L4_ast.ArrayPredExp(p,List.nth el2 0),fl2)
         | PrintPrim(p2) ->
            if List.length el2 <> 1 then die_error p "the 'print' operator takes 1 argument";
            (L4_ast.PrintExp(p,List.nth el2 0),fl2)
         | NewArrayPrim(p2) ->
            if List.length el2 <> 2 then die_error p "the 'new-array' operator takes 2 arguments";
            (L4_ast.NewArrayExp(p,List.nth el2 0,List.nth el2 1),fl2)
         | ArefPrim(p2) ->
            if List.length el2 <> 2 then die_error p "the 'aref' operator takes 2 arguments";
            (L4_ast.ArefExp(p,List.nth el2 0,List.nth el2 1),fl2)
         | AsetPrim(p2) ->
            if List.length el2 <> 3 then die_error p "the 'aset' operator takes 3 arguments";
            (L4_ast.AsetExp(p,List.nth el2 0,List.nth el2 1,List.nth el2 2,true),fl2)
         | AlenPrim(p2) ->
            if List.length el2 <> 1 then die_error p "the 'alen' operator takes 1 argument";
            (L4_ast.AlenExp(p,List.nth el2 0),fl2)
         )
      | _ ->
         let name = get_unique_symbol l5_prefix in
         let (e2,fl1) = compile_exp e in
         let f = L4_ast.Var(p,name) in
         (L4_ast.LetExp(p,f,e2,L4_ast.AppExp(p,L4_ast.ClosureProcExp(p,L4_ast.VarExp(p,f)),
            [L4_ast.ClosureVarsExp(p,L4_ast.VarExp(p,f));L4_ast.NewTupleExp(p,el2)])),fl1@fl2) )
   | PrimExp(p,pr) -> compile_prim pr true
   | IntExp(p,i) -> (L4_ast.IntExp(p,i), [])

and compile_prim (pr : L5_ast.prim) (closure : bool) : (L4_ast.exp * L4_ast.func list) =
   let (name,fname,fn,p) = (match pr with
   | PlusPrim(p) ->
      let (n,f,fn) = get_plus_func p in (n,f,fn,p)
   | MinusPrim(p) ->
      let (n,f,fn) = get_minus_func p in (n,f,fn,p)
   | TimesPrim(p) ->
      let (n,f,fn) = get_times_func p in (n,f,fn,p)
   | LtPrim(p) ->
      let (n,f,fn) = get_lt_func p in (n,f,fn,p)
   | LeqPrim(p) ->
      let (n,f,fn) = get_leq_func p in (n,f,fn,p)
   | EqPrim(p) ->
      let (n,f,fn) = get_eq_func p in (n,f,fn,p)
   | NumberPredPrim(p) ->
      let (n,f,fn) = get_numberq_func p in (n,f,fn,p)
   | ArrayPredPrim(p) ->
      let (n,f,fn) = get_arrayq_func p in (n,f,fn,p)
   | PrintPrim(p) ->
      let (n,f,fn) = get_print_func p in (n,f,fn,p)
   | NewArrayPrim(p) ->
      let (n,f,fn) = get_newarr_func p in (n,f,fn,p)
   | ArefPrim(p) ->
      let (n,f,fn) = get_aref_func p in (n,f,fn,p)
   | AsetPrim(p) ->
      let (n,f,fn) = get_aset_func p in (n,f,fn,p)
   | AlenPrim(p) ->
      let (n,f,fn) = get_alen_func p in (n,f,fn,p)
   ) in
   let ret = if closure then L4_ast.MakeClosureExp(p,name,L4_ast.NewTupleExp(p,[]))
             else L4_ast.LabelExp(p,fname) in
   (ret,fn)

and compile_var (v : L5_ast.var) : L4_ast.var = 
   match v with
   | Var(p,s) -> L4_ast.Var(p,s)
;;
