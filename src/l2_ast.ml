(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/9/2012
 *
 * L2-to-L1 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l2_ast.ml
 * This has the abstract data types for representing the
 * Abstract Syntax Tree (AST) for the parsed L2 program.
 *)

open Utils;;

let esi_id = 1;; Hashtbl.replace symbol_table "esi" esi_id;;
let edi_id = 2;; Hashtbl.replace symbol_table "edi" edi_id;;
let ebp_id = 3;; Hashtbl.replace symbol_table "ebp" ebp_id;;
let esp_id = 4;; Hashtbl.replace symbol_table "esp" esp_id;;
let eax_id = 5;; Hashtbl.replace symbol_table "eax" eax_id;;
let ecx_id = 6;; Hashtbl.replace symbol_table "ecx" ecx_id;;
let edx_id = 7;; Hashtbl.replace symbol_table "edx" edx_id;;
let ebx_id = 8;; Hashtbl.replace symbol_table "ebx" ebx_id;;

(* data type for L2 programs *)
type program = Program of pos * func list
 and func = Function of pos * int option * instr list
 and instr = 
             AssignInstr of pos * var * sval
           | MemReadInstr of pos * var * var * int32 
           | MemWriteInstr of pos * var * int32 * sval
           | PlusInstr of pos * var * tval
           | MinusInstr of pos * var * tval
           | TimesInstr of pos * var * tval
           | BitAndInstr of pos * var * tval
           | SllInstr of pos * var * svar
           | SrlInstr of pos * var * svar
           | LtInstr of pos * var * tval * tval
           | LeqInstr of pos * var * tval * tval
           | EqInstr of pos * var * tval * tval
           | LabelInstr of pos * int
           | GotoInstr of pos * int 
           | LtJumpInstr of pos * tval * tval * int * int
           | LeqJumpInstr of pos * tval * tval * int * int 
           | EqJumpInstr of pos * tval * tval * int * int 
           | CallInstr of pos * uval
           | TailCallInstr of pos * uval
           | ReturnInstr of pos
           | PrintInstr of pos * tval
           | AllocInstr of pos * tval * tval
           | ArrayErrorInstr of pos * tval * tval
 and sval = VarSVal of pos * var
          | IntSVal of pos * int32
          | LabelSVal of pos * int
 and uval = VarUVal of pos * var
          | IntUVal of pos * int32
          | LabelUVal of pos * int
 and tval = VarTVal of pos * var
          | IntTVal of pos * int32
          | LabelTVal of pos * int
 and var = VarOrReg of pos * int * bool
 and svar = IntShVal of pos * int32 
           | ShVar of pos * var
;;

let get_var_id (v : var) : int = match v with
(*   | EsiReg(_) -> esi_id
   | EdiReg(_) -> edi_id
   | EbpReg(_) -> ebp_id
   | EspReg(_) -> esp_id
   | EaxReg(_) -> eax_id
   | EcxReg(_) -> ecx_id
   | EdxReg(_) -> edx_id
   | EbxReg(_) -> ebx_id
   | Var(_,id) -> id*)
   | VarOrReg(_,id,_) -> id
;;

let is_register (id : int) : bool =
   if id < unique_id_min then true
   else false
;;

let rec get_pos_instr (i : instr) : pos = match i with
   | AssignInstr(p,_,_) -> p
   | MemReadInstr(p, _, _, _) -> p
   | MemWriteInstr(p, _, _, _) -> p
   | PlusInstr(p, _, _) -> p
   | MinusInstr(p, _, _) -> p
   | TimesInstr(p, _, _) -> p
   | BitAndInstr(p, _, _) -> p
   | SllInstr(p, _, _) -> p
   | SrlInstr(p, _, _) -> p
   | LtInstr(p, _, _, _) -> p
   | LeqInstr(p, _, _, _) -> p
   | EqInstr(p, _, _, _) -> p
   | LabelInstr(p, _) -> p
   | GotoInstr(p, _) -> p
   | LtJumpInstr(p, _, _, _, _) -> p
   | LeqJumpInstr(p, _, _, _, _) -> p
   | EqJumpInstr(p, _, _, _, _) -> p
   | CallInstr(p, _) -> p
   | TailCallInstr(p, _) -> p
   | ReturnInstr(p) -> p
   | PrintInstr(p, _) -> p
   | AllocInstr(p, _, _) -> p
   | ArrayErrorInstr(p, _, _) -> p
;; 

(* the output_... functions pretty-print L2 constructs to a specified channel *)

let rec output_program out p = match p with
  | Program(_,fl) ->
     output_string out "(\n";
     let _ = List.fold_left (fun flag f ->
        if flag then output_string out "\n";
        output_func out f;
        true
     ) false fl in ();
     output_string out "\n)"
and output_func out f = match f with
  | Function(_,n,il) -> output_string out "  (";
     (match n with
     | Some(s) -> output_string out (":"^(get_symbol s));
     | _ -> ());
     output_string out "\n";
     let _ = List.fold_left (fun flag i ->
        output_string out "    ";
        output_instr out i;
        output_string out "\n";
        true
     ) false il in ();
     output_string out "  )"
and output_instr out i = match i with
   | AssignInstr(_,r,sv) ->
      output_string out "(";
      output_var out r;
      output_string out " <- ";
      output_sval out sv;
      output_string out ")";
   | MemReadInstr(_,r1,r2,i) ->
      output_string out "(";
      output_var out r1;
      output_string out " <- (mem ";
      output_var out r2;
      output_string out " ";
      output_string out (Int32.to_string i);
      output_string out "))";
   | MemWriteInstr(_,r,i,sv) ->
      output_string out "((mem ";
      output_var out r;
      output_string out " ";
      output_string out (Int32.to_string i);
      output_string out ") <- ";
      output_sval out sv;
      output_string out ")";
   | PlusInstr(_,r,tv) ->
      output_string out "(";
      output_var out r;
      output_string out " += ";
      output_tval out tv;
      output_string out ")";
   | MinusInstr(_,r,tv) ->
      output_string out "(";
      output_var out r;
      output_string out " -= ";
      output_tval out tv;
      output_string out ")";
   | TimesInstr(_,r,tv) ->
      output_string out "(";
      output_var out r;
      output_string out " *= ";
      output_tval out tv;
      output_string out ")";
   | BitAndInstr(_,r,tv) ->
      output_string out "(";
      output_var out r;
      output_string out " &= ";
      output_tval out tv;
      output_string out ")";
   | SllInstr(_,r,sr) ->
      output_string out "(";
      output_var out r;
      output_string out " <<= ";
      output_svar out sr;
      output_string out ")";
   | SrlInstr(_,r,sr) ->
      output_string out "(";
      output_var out r;
      output_string out " >>= ";
      output_svar out sr;
      output_string out ")";
   | LtInstr(_,cr,tv1,tv2) ->
      output_string out "(";
      output_var out cr;
      output_string out " <- ";
      output_tval out tv1;
      output_string out " < ";
      output_tval out tv2;
      output_string out ")";
   | LeqInstr(_,cr,tv1,tv2) ->
      output_string out "(";
      output_var out cr;
      output_string out " <- ";
      output_tval out tv1;
      output_string out " <= ";
      output_tval out tv2;
      output_string out ")";
   | EqInstr(_,cr,tv1,tv2) ->
      output_string out "(";
      output_var out cr;
      output_string out " <- ";
      output_tval out tv1;
      output_string out " = ";
      output_tval out tv2;
      output_string out ")";
   | LabelInstr(_,s) ->
      output_string out (":"^(get_symbol s));
   | GotoInstr(_,s) ->
      output_string out "(goto :";
      output_string out (get_symbol s);
      output_string out ")";
   | LtJumpInstr(_,tv1,tv2,s1,s2) ->
      output_string out "(cjump ";
      output_tval out tv1;
      output_string out " < ";
      output_tval out tv2;
      output_string out " :";
      output_string out (get_symbol s1);
      output_string out " :";
      output_string out (get_symbol s2);
      output_string out ")";
   | LeqJumpInstr(_,tv1,tv2,s1,s2) ->
      output_string out "(cjump ";
      output_tval out tv1;
      output_string out " <= ";
      output_tval out tv2;
      output_string out " :";
      output_string out (get_symbol s1);
      output_string out " :";
      output_string out (get_symbol s2);
      output_string out ")";
   | EqJumpInstr(_,tv1,tv2,s1,s2) ->
      output_string out "(cjump ";
      output_tval out tv1;
      output_string out " = ";
      output_tval out tv2;
      output_string out " :";
      output_string out (get_symbol s1);
      output_string out " :";
      output_string out (get_symbol s2);
      output_string out ")";
   | CallInstr(_, uv) ->
      output_string out "(call ";
      output_uval out uv;
      output_string out ")";
   | TailCallInstr(_, uv) ->
      output_string out "(tail-call ";
      output_uval out uv;
      output_string out ")";
   | ReturnInstr(_) ->
      output_string out "(return)";
   | PrintInstr(_, tv) ->
      output_string out "(eax <- (print ";
      output_tval out tv;
      output_string out "))";
   | AllocInstr(_, tv1, tv2) ->
      output_string out "(eax <- (allocate ";
      output_tval out tv1;
      output_string out " ";
      output_tval out tv2;
      output_string out "))";
   | ArrayErrorInstr(_, tv1, tv2) ->
      output_string out "(eax <- (array-error ";
      output_tval out tv1;
      output_string out " ";
      output_tval out tv2;
      output_string out "))";
and output_var out r = match r with
   | VarOrReg(_,id,_) -> output_string out (get_symbol id)
and output_svar out sr = match sr with
   | IntShVal(_,i) -> output_string out (Int32.to_string i)
   | ShVar(_,v) -> output_var out v
and output_sval out s = match s with
   | VarSVal(_, r) -> output_var out r
   | IntSVal(_, i) -> output_string out (Int32.to_string i)
   | LabelSVal(_,s) -> output_string out (":"^(get_symbol s))
and output_uval out u = match u with
   | VarUVal(_,r) -> output_var out r
   | IntUVal(_, i) -> output_string out (Int32.to_string i)
   | LabelUVal(_,s) -> output_string out (":"^(get_symbol s))
and output_tval out t = match t with
   | VarTVal(_,r) -> output_var out r
   | IntTVal(_,i) -> output_string out (Int32.to_string i)
   | LabelTVal(_,s) -> output_string out (":"^(get_symbol s))
;;

(* the print_... functions pretty-print L2 constructs to stdout *)

let rec print_program p = output_program stdout p
and print_func f = output_func stdout f
and print_instr i = output_instr stdout i
and print_var r = output_var stdout r
and print_svar sr = output_svar stdout sr
and print_sval s = output_sval stdout s
and print_uval u = output_uval stdout u
and print_tval t = output_tval stdout t
;;

(* "type-cast" functions *)

let get_tval (sv : sval) : tval = 
   match sv with
   | VarSVal(p,v) -> VarTVal(p,v)
   | IntSVal(p,i) -> IntTVal(p,i)
   | LabelSVal(p,l) -> LabelTVal(p,l)
;;

let get_uval (sv : sval) : uval = 
   match sv with
   | VarSVal(p,v) -> VarUVal(p,v)
   | IntSVal(p,i) -> IntUVal(p,i)
   | LabelSVal(p,l) -> LabelUVal(p,l)
;;

let get_var (sv : sval) : var =
   let msg = "expected a variable, not a constant" in
   match sv with
   | VarSVal(p,v) -> v
   | IntSVal(p,_) -> die_error p msg
   | LabelSVal(p,_) -> die_error p msg
;;
