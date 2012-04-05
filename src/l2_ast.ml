(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/3/2012
 *
 * L1-to-assembly Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l2_ast.ml
 * This has the abstract data types for representing the
 * Abstract Syntax Tree (AST) for the parsed L1 program.
 *)

open Utils;;

(* data type for L1 programs *)
type program = Program of pos * func list
 and func = Function of pos * string option * instr list
 and instr = 
             AssignInstr of pos * var * sval
           | MemReadInstr of pos * var * var * int64 
           | MemWriteInstr of pos * var * int64 * sval
           | PlusInstr of pos * var * tval
           | MinusInstr of pos * var * tval
           | TimesInstr of pos * var * tval
           | BitAndInstr of pos * var * tval
           | SllInstr of pos * var * svar
           | SrlInstr of pos * var * svar
           | LtInstr of pos * var * tval * tval
           | LeqInstr of pos * var * tval * tval
           | EqInstr of pos * var * tval * tval
           | LabelInstr of pos * string
           | GotoInstr of pos * string
           | LtJumpInstr of pos * tval * tval * string * string
           | LeqJumpInstr of pos * tval * tval * string * string
           | EqJumpInstr of pos * tval * tval * string * string
           | CallInstr of pos * uval
           | TailCallInstr of pos * uval
           | ReturnInstr of pos
           | PrintInstr of pos * tval
           | AllocInstr of pos * tval * tval
           | ArrayErrorInstr of pos * tval * tval
 and sval = VarSVal of pos * var
          | IntSVal of pos * int64
          | LabelSVal of pos * string
 and uval = VarUVal of pos * var
          | LabelUVal of pos * string
 and tval = VarTVal of pos * var
          | IntTVal of pos * int64
 and var = EsiReg of pos
         | EdiReg of pos
         | EbpReg of pos
         | EspReg of pos
         | EaxReg of pos
         | EcxReg of pos
         | EdxReg of pos
         | EbxReg of pos
         | Var of pos * string (* TODO XXX - eventually we need a symbol table *)
 and svar = IntShVal of pos * int64 
           | ShVar of pos * var
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
     | Some(s) -> output_string out (":"^s);
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
      output_string out (Int64.to_string i);
      output_string out "))";
   | MemWriteInstr(_,r,i,sv) ->
      output_string out "((mem ";
      output_var out r;
      output_string out " ";
      output_string out (Int64.to_string i);
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
      output_string out (":"^s);
   | GotoInstr(_,s) ->
      output_string out "(goto ";
      output_string out s;
      output_string out ")";
   | LtJumpInstr(_,tv1,tv2,s1,s2) ->
      output_string out "(cjump ";
      output_tval out tv1;
      output_string out " < ";
      output_tval out tv2;
      output_string out " :";
      output_string out s1;
      output_string out " :";
      output_string out s2;
      output_string out ")";
   | LeqJumpInstr(_,tv1,tv2,s1,s2) ->
      output_string out "(cjump ";
      output_tval out tv1;
      output_string out " <= ";
      output_tval out tv2;
      output_string out " :";
      output_string out s1;
      output_string out " :";
      output_string out s2;
      output_string out ")";
   | EqJumpInstr(_,tv1,tv2,s1,s2) ->
      output_string out "(cjump ";
      output_tval out tv1;
      output_string out " = ";
      output_tval out tv2;
      output_string out " :";
      output_string out s1;
      output_string out " :";
      output_string out s2;
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
   | EsiReg(_) -> output_string out "esi"
   | EdiReg(_) -> output_string out "edi"
   | EbpReg(_) -> output_string out "ebp"
   | EspReg(_) -> output_string out "esp"
   | EaxReg(_) -> output_string out "eax"
   | EcxReg(_) -> output_string out "ecx"
   | EdxReg(_) -> output_string out "edx"
   | EbxReg(_) -> output_string out "ebx"
   | Var(_,s) -> output_string out s
and output_svar out sr = match sr with
   | IntShVal(_,i) -> output_string out (Int64.to_string i)
   | ShVar(_,v) -> output_var out v
and output_sval out s = match s with
   | VarSVal(_, r) -> output_var out r
   | IntSVal(_, i) -> output_string out (Int64.to_string i)
   | LabelSVal(_,s) -> output_string out (":"^s)
and output_uval out u = match u with
   | VarUVal(_,r) -> output_var out r
   | LabelUVal(_,s) -> output_string out (":"^s)
and output_tval out t = match t with
   | VarTVal(_,r) -> output_var out r
   | IntTVal(_,i) -> output_string out (Int64.to_string i)
;;

(* the print_... functions pretty-print L1 constructs to stdout *)

let rec print_program p = output_program stdout p
and print_func f = output_func stdout f
and print_instr i = output_instr stdout i
and print_var r = output_var stdout r
and print_svar sr = output_svar stdout sr
and print_sval s = output_sval stdout s
and print_uval u = output_uval stdout u
and print_tval t = output_tval stdout t
;;