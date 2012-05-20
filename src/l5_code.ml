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

let fast_prefix = "FAST";;

let rec make_var_list (p : pos) (prefix : string) (n : int) : L4_ast.var list =
   if n = 0 then []
   else if n = 1 then [L4_ast.Var(p,prefix^(string_of_int n))]
   else (
      (make_var_list p prefix (n-1))@[L4_ast.Var(p,prefix^(string_of_int n))]
   )
;;

let get_func (p : pos) (nm : string) (num : int) (fn : ((string * string) option) ref) :
(string * string * L4_ast.var list * L4_ast.var list * L4_ast.var option) =
   match !fn with
   | None ->
      let name = make_ident_unique l5_prefix nm in
      let fname = make_ident_unique l5_prefix (fast_prefix^nm) in
      fn := Some(name,fname);
      let fv = L4_ast.Var(p,"fv") in
      let bv = L4_ast.Var(p,"bv") in
      let fvars = make_var_list p "p" num in 
      (name,fname,[fv;bv],fvars,Some(bv))
   | Some(s1,s2) -> (s1,s2,[],[],None)
;;

let plus_func_name = ref (None : (string * string) option);;
let get_plus_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "plus" 2 plus_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.PlusExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.PlusExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let minus_func_name = ref (None : (string * string) option);;
let get_minus_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "minus" 2 minus_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.MinusExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.MinusExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let times_func_name = ref (None : (string * string) option);;
let get_times_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "times" 2 times_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.TimesExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.TimesExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let lt_func_name = ref (None : (string * string) option);;
let get_lt_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "lt" 2 lt_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.LtExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.LtExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let leq_func_name = ref (None : (string * string) option);;
let get_leq_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "leq" 2 leq_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.LeqExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.LeqExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let eq_func_name = ref (None : (string * string) option);;
let get_eq_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "eq" 2 eq_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.EqExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.EqExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let numberq_func_name = ref (None : (string * string) option);;
let get_numberq_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "numberq" 1 numberq_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.NumberPredExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.NumberPredExp(p,L4_ast.VarExp(p,List.nth fvars 0)))
            ])
   | _ -> (name,fname,[])
;;

let arrayq_func_name = ref (None : (string * string) option);;
let get_arrayq_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "arrayq" 1 arrayq_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.ArrayPredExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.ArrayPredExp(p,L4_ast.VarExp(p,List.nth fvars 0)))
            ])
   | _ -> (name,fname,[])
;;

let print_func_name = ref (None : (string * string) option);;
let get_print_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "print" 1 print_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.PrintExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.PrintExp(p,L4_ast.VarExp(p,List.nth fvars 0)))
            ])
   | _ -> (name,fname,[])
;;

let newarr_func_name = ref (None : (string * string) option);;
let get_newarr_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "newarr" 2 newarr_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.NewArrayExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.NewArrayExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let aref_func_name = ref (None : (string * string) option);;
let get_aref_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "aref" 2 aref_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.ArefExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.ArefExp(p,L4_ast.VarExp(p,List.nth fvars 0),L4_ast.VarExp(p,List.nth fvars 1)))
            ])
   | _ -> (name,fname,[])
;;

let aset_func_name = ref (None : (string * string) option);;
let get_aset_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "aset" 3 aset_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.AsetExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,1L)),
                              L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,3L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.AsetExp(p,L4_ast.VarExp(p,List.nth fvars 0),
                              L4_ast.VarExp(p,List.nth fvars 1),
                              L4_ast.VarExp(p,List.nth fvars 2)))
            ])
   | _ -> (name,fname,[])
;;

let alen_func_name = ref (None : (string * string) option);;
let get_alen_func (p : pos) : (string * string * L4_ast.func list) =
   let (name,fname,vars,fvars,bvo) = get_func p "alen" 1 alen_func_name in
   match bvo with
   | Some(bv) ->
      (name,fname,[L4_ast.Function(p,name,vars,
             L4_ast.AlenExp(p,L4_ast.ArefExp(p,L4_ast.VarExp(p,bv),L4_ast.IntExp(p,0L))));
             L4_ast.Function(p,fname,fvars,
             L4_ast.AlenExp(p,L4_ast.VarExp(p,List.nth fvars 0)))
            ])
   | _ -> (name,fname,[])
;;

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
      let (el2,fl2) = List.fold_left (fun (elx,flx) ex ->
         let (et,flt) = compile_exp ex in
         (elx@[et], flx@flt)
      ) ([],[]) el in
      (match e with
      | PrimExp(p,pr) ->
         let (ex,fl) = compile_prim pr false in
         (L4_ast.AppExp(p,ex,el2),fl@fl2)
      | _ ->
         let name = get_unique_ident l5_prefix in
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
