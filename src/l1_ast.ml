(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/3/2012
 *
 * L1-to-assembly Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l1_ast.ml
 * This has the abstract data types for representing the
 * Abstract Syntax Tree (AST) for the parsed L1 program.
 *)

open Utils;;

(* data type for L1 programs *)
type program = Program of pos * func list
 and func = Function of pos * int option * instr list
 and instr = 
             AssignInstr of pos * reg * sval
           | MemReadInstr of pos * reg * reg * int32 
           | MemWriteInstr of pos * reg * int32 * sval
           | PlusInstr of pos * reg * tval
           | MinusInstr of pos * reg * tval
           | TimesInstr of pos * reg * tval
           | BitAndInstr of pos * reg * tval
           | SllInstr of pos * reg * sreg
           | SrlInstr of pos * reg * sreg
           | LtInstr of pos * creg * tval * tval
           | LeqInstr of pos * creg * tval * tval
           | EqInstr of pos * creg * tval * tval
           | LabelInstr of pos * int 
           | GotoInstr of pos * int
           | LtJumpInstr of pos * tval * tval * int * int
           | LeqJumpInstr of pos * tval * tval * int * int 
           | EqJumpInstr of pos * tval * tval * int * int
           | CallInstr of pos * uval
           | TailCallInstr of pos * uval
           | ReturnInstr of pos
           | PrintInstr of pos * tval
           | PrintStrInstr of pos * tval
           | AllocInstr of pos * tval * tval
           | StringInstr of pos * int
           | ArrayErrorInstr of pos * tval * tval
 and reg = EsiReg of pos
         | EdiReg of pos
         | EbpReg of pos
         | EspReg of pos
         | CallerSaveReg of pos * creg
 and creg = EaxReg of pos
          | EcxReg of pos
          | EdxReg of pos
          | EbxReg of pos
 and sreg = EcxShReg of pos
           | IntShVal of pos * int32 
 and sval = RegSVal of pos * reg
          | IntSVal of pos * int32
          | LabelSVal of pos * int
 and uval = RegUVal of pos * reg
          | IntUVal of pos * int32
          | LabelUVal of pos * int
 and tval = RegTVal of pos * reg
          | IntTVal of pos * int32
          | LabelTVal of pos * int
;;

(* the output_... functions pretty-print L1 constructs to a specified channel *)

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
      output_reg out r;
      output_string out " <- ";
      output_sval out sv;
      output_string out ")";
   | MemReadInstr(_,r1,r2,i) ->
      output_string out "(";
      output_reg out r1;
      output_string out " <- (mem ";
      output_reg out r2;
      output_string out " ";
      output_string out (Int32.to_string i);
      output_string out "))";
   | MemWriteInstr(_,r,i,sv) ->
      output_string out "((mem ";
      output_reg out r;
      output_string out " ";
      output_string out (Int32.to_string i);
      output_string out ") <- ";
      output_sval out sv;
      output_string out ")";
   | PlusInstr(_,r,tv) ->
      output_string out "(";
      output_reg out r;
      output_string out " += ";
      output_tval out tv;
      output_string out ")";
   | MinusInstr(_,r,tv) ->
      output_string out "(";
      output_reg out r;
      output_string out " -= ";
      output_tval out tv;
      output_string out ")";
   | TimesInstr(_,r,tv) ->
      output_string out "(";
      output_reg out r;
      output_string out " *= ";
      output_tval out tv;
      output_string out ")";
   | BitAndInstr(_,r,tv) ->
      output_string out "(";
      output_reg out r;
      output_string out " &= ";
      output_tval out tv;
      output_string out ")";
   | SllInstr(_,r,sr) ->
      output_string out "(";
      output_reg out r;
      output_string out " <<= ";
      output_sreg out sr;
      output_string out ")";
   | SrlInstr(_,r,sr) ->
      output_string out "(";
      output_reg out r;
      output_string out " >>= ";
      output_sreg out sr;
      output_string out ")";
   | LtInstr(_,cr,tv1,tv2) ->
      output_string out "(";
      output_creg out cr;
      output_string out " <- ";
      output_tval out tv1;
      output_string out " < ";
      output_tval out tv2;
      output_string out ")";
   | LeqInstr(_,cr,tv1,tv2) ->
      output_string out "(";
      output_creg out cr;
      output_string out " <- ";
      output_tval out tv1;
      output_string out " <= ";
      output_tval out tv2;
      output_string out ")";
   | EqInstr(_,cr,tv1,tv2) ->
      output_string out "(";
      output_creg out cr;
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
   | PrintStrInstr(_, tv) ->
      output_string out "(eax <- (print-string ";
      output_tval out tv;
      output_string out "))";
   | AllocInstr(_, tv1, tv2) ->
      output_string out "(eax <- (allocate ";
      output_tval out tv1;
      output_string out " ";
      output_tval out tv2;
      output_string out "))";
   | StringInstr(_, s) ->
      output_string out "(eax <- ";
      output_stringlit out (Printf.sprintf "%S" (get_symbol s));
      output_string out ")";
   | ArrayErrorInstr(_, tv1, tv2) ->
      output_string out "(eax <- (array-error ";
      output_tval out tv1;
      output_string out " ";
      output_tval out tv2;
      output_string out "))";
and output_reg out r = match r with
   | EsiReg(_) -> output_string out "esi"
   | EdiReg(_) -> output_string out "edi"
   | EbpReg(_) -> output_string out "ebp"
   | EspReg(_) -> output_string out "esp"
   | CallerSaveReg(_, cr) -> output_creg out cr
and output_creg out cr = match cr with
   | EaxReg(_) -> output_string out "eax"
   | EcxReg(_) -> output_string out "ecx"
   | EdxReg(_) -> output_string out "edx"
   | EbxReg(_) -> output_string out "ebx"
and output_sreg out sr = match sr with
   | EcxShReg(_) -> output_string out "ecx"
   | IntShVal(_,i) -> output_string out (Int32.to_string i)
and output_sval out s = match s with
   | RegSVal(_, r) -> output_reg out r
   | IntSVal(_, i) -> output_string out (Int32.to_string i)
   | LabelSVal(_,s) -> output_string out (":"^(get_symbol s))
and output_uval out u = match u with
   | RegUVal(_,r) -> output_reg out r
   | IntUVal(_, i) -> output_string out (Int32.to_string i)
   | LabelUVal(_,s) -> output_string out (":"^(get_symbol s))
and output_tval out t = match t with
   | RegTVal(_,r) -> output_reg out r
   | IntTVal(_,i) -> output_string out (Int32.to_string i)
   | LabelTVal(_,s) -> output_string out (":"^(get_symbol s))
and output_stringlit out s =
   output_string out s (* TODO - encode special chars *)
;;

(* the print_... functions pretty-print L1 constructs to stdout *)

let rec print_program p = output_program stdout p
and print_func f = output_func stdout f
and print_instr i = output_instr stdout i
and print_reg r = output_reg stdout r
and print_creg cr = output_creg stdout cr
and print_sreg sr = output_sreg stdout sr
and print_sval s = output_sval stdout s
and print_uval u = output_uval stdout u
and print_tval t = output_tval stdout t
and print_stringlit s = output_stringlit stdout s
;;

(* "casts" a reg to a creg *)
let get_creg r = match r with
   | CallerSaveReg(_,c) -> c
   | _ -> parse_error "destination must be one of eax, ecx, edx, ebx"
;;

let is_tval_const (tv : tval) : bool =
   match tv with
   | RegTVal(_,_) -> false
   | _ -> true
;;

let get_lower_creg (cr : creg) : string =
   match cr with
   | EaxReg(_) -> "%al"
   | EcxReg(_) -> "%cl"
   | EdxReg(_) -> "%dl"
   | EbxReg(_) -> "%bl"
;;
