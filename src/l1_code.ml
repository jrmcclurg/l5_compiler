(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/3/2012
 *
 * L1-to-assembly Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * code.ml
 * This has all the functionality for generating
 * the C runtime and assembly code, and utilities
 * for issuing the compile/link system calls.
 *)

open Flags;;
open L1_ast;;
open Utils;;
open Unix;;

let debug_enabled () =
   let result = has_debug "1" in 
   result
;;

(*
 * the compile_... functions generate x86 assembly code based on
 * L1 program constructs and writes the code to the output channel o
 *)

(* compiles an L1 "p" nonterminal into x86 assembly *)
let rec compile_program (o : out_channel) (p : program) : unit = match p with
   | Program(ps, fl) ->
      (* output some boilerplate for the assembly file *)
      output_string o "	.file	\"prog.c\"\n" ;
      output_string o "	.text\n" ;
      output_string o "########## begin code ##########\n";
      (* start outputting the functions (the first function will be "go") *)
      output_string o "go:\n" ;
      output_string o "\n";
      (* iterate through the functions, giving each a unique number k *)
      let _ = List.fold_left (fun k f ->
         compile_function o f (k = 1) k;
         output_string o "\n";
         k+1
      ) 1 fl in ();
      output_string o "########## end code ##########\n";
      (* output some boilerplate for the assembly file *)
      output_string o "	.ident	\"GCC: (Ubuntu 4.3.2-1ubuntu12) 4.3.2\"\n" ;
      output_string o "	.section	.note.GNU-stack,\"\",@progbits\n" ;

(*
 * compiles an L1 "(i ...)" or "(label i ...)" expression into x86 assembly
 *
 * first - should be true if this is the first function in the L1 program
 * j     - should be a unique integer
 *)
and compile_function (o : out_channel) (f : func) (first : bool) (j : int) : unit = match f with
   | Function(ps, so, il) ->
      (* if it's the first function, then it's name must be "go") *)
      let name = (if first then "go" else (match so with
        | None -> die_error ps "function must be named"
        | Some(s) -> ("_"^(get_symbol s)))) in
      (* output some boilerplate if we're processing the "go" function *)
      if first then (
      output_string o ("	.globl	"^name^"\n") ;
      output_string o ("	.type	"^name^", @function\n")  );
      (* output the label for the start of the function *)
      output_string o ("########## begin function \""^name^"\" ##########\n");
      output_string o (name^":\n") ;
      (* output some more boilerplate if we're processing the "go" function *)
      if first then (
      output_string o "        # save caller's base pointer\n" ;
      output_string o "        pushl   %ebp\n" ;
      output_string o "        movl    %esp, %ebp\n" ;
      output_string o "\n" ;
      output_string o "        # save callee-saved registers\n" ;
      output_string o "        pushl   %ebx\n" ;
      output_string o "        pushl   %esi\n" ;
      output_string o "        pushl   %edi\n" ;
      output_string o "        pushl   %ebp\n" ;
      output_string o "\n" ;
      output_string o "        # body begins with base and\n" ;
      output_string o "        # stack pointers equal\n" ;
      output_string o "        movl    %esp, %ebp\n" ;
      output_string o "\n" ;
      output_string o "        ##### begin function body #####\n" );
      (* if the "go" function (i.e. the first one) had a label, we need 
       * to add it to the instruction list, since we ignored it when
       * just using the name "go" *)
      let il2 = if first then (match so with
      | None -> il
      | Some(l) -> LabelInstr(ps,l)::il) else il in
      (* iterate through the instructions, and compile them, giving
       * each a unique number k *)
      let _ = List.fold_left (fun k i ->
         compile_instr o i first j k;
         k+1
      ) 1 il2 in ();
      (* output some boilerplate if we're processing the "go" function *)
      if first then (
      output_string o "        ##### end function body #####\n" ;
      output_string o "\n" ;
      output_string o "        # restore callee-saved registers\n" ;
      output_string o "        popl   %ebp\n" ;
      output_string o "        popl   %edi\n" ;
      output_string o "        popl   %esi\n" ;
      output_string o "        popl   %ebx\n" ;
      output_string o "\n" ;
      output_string o "        # restore caller's base pointer\n" ;
      output_string o "        leave\n" ;
      output_string o "        ret\n" );
      (* output the footer comment for the function *)
      output_string o ("########## end function \""^name^"\" ##########\n");
      (* output some boilerplate if we're processing the "go" function *)
      if first then (output_string o ("	.size	"^name^", .-"^name^"\n") )

(*
 * compiles an L1 instruction expression into x86 assembly
 * 
 * first - should be true if this is the first instruction in a L1 function
 * j     - should correspond to the parent function's unique number
 * k     - should be a unique number for this instruction
 *
 * The j,k numbers are used to generate unique return addresses of the form
 *    r_j_k
 * For example, if we look at the 5th instruction in the 1st L1 function,
 * and we find a call, the return address label will be
 *    r_1_5:
 *)
and compile_instr (o : out_channel) (i : instr) (first : bool) (j : int) (k : int) : unit =
   output_string o "\t# ";
   output_instr o i;
   output_string o "\n";
   match i with
   | AssignInstr(ps,r,sv) -> 
      (* movl sv, r *)
      output_string o ("\t"^"movl"^"\t");
      compile_sval o sv;
      output_string o ", ";
      compile_reg o r;
      output_string o "\n";
   | MemReadInstr(ps,r,br,off) ->
      (* movl off(br), r *)
      output_string o ("\t"^"movl"^"\t");
      output_string o (Int64.to_string off);
      output_string o "(";
      compile_reg o br;
      output_string o "), ";
      compile_reg o r;
      output_string o "\n";
   | MemWriteInstr(ps,br,off,sv) ->
      (* movl sv, off(br) *)
      output_string o ("\t"^"movl"^"\t");
      compile_sval o sv;
      output_string o ", ";
      output_string o (Int64.to_string off);
      output_string o "(";
      compile_reg o br;
      output_string o ")\n";
   | PlusInstr(ps,r,tv) -> 
      (* addl tv, r *)
      output_string o ("\t"^"addl"^"\t");
      compile_tval o tv;
      output_string o ", ";
      compile_reg o r;
      output_string o "\n";
   | MinusInstr(ps,r,tv) -> 
      (* subl tv, r *)
      output_string o ("\t"^"subl"^"\t");
      compile_tval o tv;
      output_string o ", ";
      compile_reg o r;
      output_string o "\n";
   | TimesInstr(ps,r,tv) -> 
      (* imull tv, r *)
      output_string o ("\t"^"imull"^"\t");
      compile_tval o tv;
      output_string o ", ";
      compile_reg o r;
      output_string o "\n";
   | BitAndInstr(ps,r,tv) -> 
      (* andl tv, r *)
      output_string o ("\t"^"andl"^"\t");
      compile_tval o tv;
      output_string o ", ";
      compile_reg o r;
      output_string o "\n";
   | SllInstr(ps,r,sr) ->
      (* sall sr_lower, r *)
      (* (where sr_lower is the lower byte of sr) *)
      output_string o ("\t"^"sall"^"\t");
      (match sr with
      | EcxShReg(_) -> output_string o "%cl" (* lower 8 bits of ecx *)
      | IntShVal(_,_) -> compile_sreg o sr);
      output_string o ", ";
      compile_reg o r;
      output_string o "\n";
   | SrlInstr(ps,r,sr) ->
      (* sarl sr_lower, r *)
      (* (where sr_lower is the lower byte of sr) *)
      output_string o ("\t"^"sarl"^"\t");
      (match sr with
      | EcxShReg(_) -> output_string o "%cl" (* lower 8 bits of ecx *)
      | IntShVal(_,_) -> compile_sreg o sr);
      output_string o ", ";
      compile_reg o r;
      output_string o "\n";
   | LtInstr(ps,cr,tv1,tv2) ->
      let lower = (get_lower_creg cr) in
      (* if tv1 is constant, we must reverse the operation,
       * since the second operand of cmp must be a register.
       * if both tv1,tv2 are constants, we use cr as a temp
       * for tv1 *)
      let c1 = (is_tval_const tv1) in (* whether tv1 is a constant *)
      let c2 = (is_tval_const tv2) in (* whether tv2 is a constant *)
      let (r1,r2,create,reverse) = if (c1 && c2) then (RegTVal(ps,CallerSaveReg(ps,cr)),tv2,true,false)
                                   else if c1 then (tv2,tv1,false,true) else (tv1,tv2,false,false) in
      if create then (
         (* movl tv1, r1 *)
         output_string o ("\t"^"movl"^"\t");
         compile_tval o tv1;
         output_string o ", ";
         compile_tval o r1;
         output_string o "\n"
      );
      (* cmp tv2, r1 *)
      output_string o ("\t"^"cmp"^"\t");
      compile_tval o r2;
      output_string o ", ";
      compile_tval o r1;
      output_string o "\n";
      (* setl cr_lower (or setg cr_lower if reverse) *)
      output_string o ("\t"^"set"^(if reverse then "g" else "l")^"\t"^lower^"\n");
      (* movzbl cr_lower, cr *)
      output_string o ("\t"^"movzbl"^"\t"^lower^", ");
      compile_creg o cr;
      output_string o "\n"
   | LeqInstr(ps,cr,tv1,tv2) ->
      let lower = (get_lower_creg cr) in
      (* if tv1 is constant, we must reverse the operation,
       * since the second operand of cmp must be a register.
       * if both tv1,tv2 are constants, we use cr as a temp
       * for tv1 *)
      let c1 = (is_tval_const tv1) in (* whether tv1 is a constant *)
      let c2 = (is_tval_const tv2) in (* whether tv2 is a constant *)
      let (r1,r2,create,reverse) = if (c1 && c2) then (RegTVal(ps,CallerSaveReg(ps,cr)),tv2,true,false)
                                   else if c1 then (tv2,tv1,false,true) else (tv1,tv2,false,false) in
      if create then (
         (* movl tv1, r1 *)
         output_string o ("\t"^"movl"^"\t");
         compile_tval o tv1;
         output_string o ", ";
         compile_tval o r1;
         output_string o "\n"
      );
      (* cmp tv2, r1 *)
      output_string o ("\t"^"cmp"^"\t");
      compile_tval o r2;
      output_string o ", ";
      compile_tval o r1;
      output_string o "\n";
      (* setle cr_lower (or setge cr_lower if reverse) *)
      output_string o ("\t"^"set"^(if reverse then "g" else "l")^"e"^"\t"^lower^"\n");
      (* movzbl cr_lower, cr *)
      output_string o ("\t"^"movzbl"^"\t"^lower^", ");
      compile_creg o cr;
      output_string o "\n"
   | EqInstr(ps,cr,tv1,tv2) ->
      let lower = (get_lower_creg cr) in
      (* if tv1 is constant, we must reverse the operation,
       * since the second operand of cmp must be a register.
       * if both tv1,tv2 are constants, we use cr as a temp
       * for tv1 *)
      let c1 = (is_tval_const tv1) in (* whether tv1 is a constant *)
      let c2 = (is_tval_const tv2) in (* whether tv2 is a constant *)
      let (r1,r2,create) = if (c1 && c2) then (RegTVal(ps,CallerSaveReg(ps,cr)),tv2,true)
                                   else if c1 then (tv2,tv1,false) else (tv1,tv2,false) in
      if create then (
         (* movl tv1, r1 *)
         output_string o ("\t"^"movl"^"\t");
         compile_tval o tv1;
         output_string o ", ";
         compile_tval o r1;
         output_string o "\n"
      );
      (* cmp tv2, r1 *)
      output_string o ("\t"^"cmp"^"\t");
      compile_tval o r2;
      output_string o ", ";
      compile_tval o r1;
      output_string o "\n";
      (* sete cr_lower *)
      output_string o ("\t"^"sete"^"\t"^lower^"\n");
      (* movzbl cr_lower, cr *)
      output_string o ("\t"^"movzbl"^"\t"^lower^", ");
      compile_creg o cr;
      output_string o "\n"
   | LabelInstr(ps,l) ->
      (* l: *)
      compile_label o l
   | GotoInstr(ps,s) ->
      (* jmp _l *)
      output_string o ("\t"^"jmp"^"\t"^"_");
      output_string o (get_symbol s);
      output_string o "\n"
   | LtJumpInstr(ps,tv1,tv2,s1,s2) ->
      (* if tv1 is constant, we must reverse the operation,
       * since the second operand of cmp must be a register.
       * if both are constants, record eax on the stack,
       * use it as a temp, then restore it *)
         let c1 = (is_tval_const tv1) in (* whether tv1 is a constant *)
         let c2 = (is_tval_const tv2) in (* whether tv2 is a constant *)
         let (r1,r2,create,reverse) = if (c1 && c2) then (RegTVal(ps,CallerSaveReg(ps,EaxReg(ps))),tv2,true,false)
                                      else if c1 then (tv2,tv1,false,true) else (tv1,tv2,false,false) in
         (* movl tv1, r1 (or nothing if reverse) *)
         if create then (
            (* push r1 *)
            output_string o ("\t"^"push"^"\t"^"%");
            output_tval o r1;
            output_string o "\n";
            (* movl tv1, r1 *)
            output_string o ("\t"^"movl"^"\t");
            compile_tval o tv1;
            output_string o ", ";
            compile_tval o r1;
            output_string o "\n"
         );
         (* cmp tv2, r1 *)
         output_string o ("\t"^"cmp"^"\t");
         compile_tval o r2;
         output_string o ", ";
         compile_tval o r1;
         output_string o "\n";
         if create then (
            (* pop r1 *)
            output_string o ("\t"^"pop"^"\t"^"%");
            output_tval o r1;
            output_string o "\n"
         );
         (* jl s1 (or jg s1 if reverse) *)
         output_string o ("\t"^"j"^(if reverse then "g" else "l")^"\t"^"_");
         output_string o (get_symbol s1);
         output_string o "\n";
         (* jmp s2 *)
         output_string o ("\t"^"jmp"^"\t"^"_");
         output_string o (get_symbol s2);
         output_string o "\n" 
   | LeqJumpInstr(ps,tv1,tv2,s1,s2) ->
      (* if tv1 is constant, we must reverse the operation,
       * since the second operand of cmp must be a register.
       * if both are constants, record eax on the stack,
       * use it as a temp, then restore it *)
         let c1 = (is_tval_const tv1) in (* whether tv1 is a constant *)
         let c2 = (is_tval_const tv2) in (* whether tv2 is a constant *)
         let (r1,r2,create,reverse) = if (c1 && c2) then (RegTVal(ps,CallerSaveReg(ps,EaxReg(ps))),tv2,true,false)
                                      else if c1 then (tv2,tv1,false,true) else (tv1,tv2,false,false) in
         (* movl tv1, r1 (or nothing if reverse) *)
         if create then (
            (* push r1 *)
            output_string o ("\t"^"push"^"\t"^"%");
            output_tval o r1;
            output_string o "\n";
            (* movl tv1, r1 *)
            output_string o ("\t"^"movl"^"\t");
            compile_tval o tv1;
            output_string o ", ";
            compile_tval o r1;
            output_string o "\n"
         );
         (* cmp tv2, r1 *)
         output_string o ("\t"^"cmp"^"\t");
         compile_tval o r2;
         output_string o ", ";
         compile_tval o r1;
         output_string o "\n";
         if create then (
            (* pop r1 *)
            output_string o ("\t"^"pop"^"\t"^"%");
            output_tval o r1;
            output_string o "\n"
         );
         (* jle s1 (or jge s1 if reverse) *)
         output_string o ("\t"^"j"^(if reverse then "g" else "l")^"e"^"\t"^"_");
         output_string o (get_symbol s1);
         output_string o "\n";
         (* jmp s2 *)
         output_string o ("\t"^"jmp"^"\t"^"_");
         output_string o (get_symbol s2);
         output_string o "\n" 
   | EqJumpInstr(ps,tv1,tv2,s1,s2) ->
      (* if tv1 is constant, we must reverse the operation,
       * since the second operand of cmp must be a register.
       * if both are constants, record eax on the stack,
       * use it as a temp, then restore it *)
         let c1 = (is_tval_const tv1) in (* whether tv1 is a constant *)
         let c2 = (is_tval_const tv2) in (* whether tv2 is a constant *)
         let (r1,r2,create,reverse) = if (c1 && c2) then (RegTVal(ps,CallerSaveReg(ps,EaxReg(ps))),tv2,true,false)
                                      else if c1 then (tv2,tv1,false,true) else (tv1,tv2,false,false) in
         (* movl tv1, r1 (or nothing if reverse) *)
         if create then (
            (* push r1 *)
            output_string o ("\t"^"push"^"\t"^"%");
            output_tval o r1;
            output_string o "\n";
            (* movl tv1, r1 *)
            output_string o ("\t"^"movl"^"\t");
            compile_tval o tv1;
            output_string o ", ";
            compile_tval o r1;
            output_string o "\n"
         );
         (* cmp tv2, r1 *)
         output_string o ("\t"^"cmp"^"\t");
         compile_tval o r2;
         output_string o ", ";
         compile_tval o r1;
         output_string o "\n";
         if create then (
            (* pop r1 *)
            output_string o ("\t"^"pop"^"\t"^"%");
            output_tval o r1;
            output_string o "\n"
         );
         (* je s1 *)
         output_string o ("\t"^"je"^"\t"^"_");
         output_string o (get_symbol s1);
         output_string o "\n";
         (* jmp s2 *)
         output_string o ("\t"^"jmp"^"\t"^"_");
         output_string o (get_symbol s2);
         output_string o "\n" 
   | CallInstr(ps, uv) ->
      (* pushl $r_j_k *)
      output_string o ("\t"^"pushl"^"\t"^"$r_"^(string_of_int j)^(string_of_int k)^"\n");
      (* pushl %ebp *)
      output_string o ("\t"^"pushl"^"\t"^"%ebp"^"\n");
      (* movl %esp, %ebp *)
      output_string o ("\t"^"movl"^"\t"^"%esp, %ebp"^"\n");
      (* jmp uv *)
      output_string o ("\t"^"jmp"^"\t");
      compile_uval o uv;
      output_string o "\n";
      (* r_j_k: *)
      output_string o ("r_"^(string_of_int j)^(string_of_int k)^":"^"\n");
   | TailCallInstr(ps, uv) ->
      (* movl %ebp, %esp *)
      output_string o ("\t"^"movl"^"\t"^"%ebp, %esp"^"\n");
      (* jmp uv *)
      output_string o ("\t"^"jmp"^"\t");
      compile_uval o uv;
      output_string o "\n";
   | ReturnInstr(ps) ->
      (* if this is a "return" in the "go" function, we are called
       * from C, so we need to follow the C-style function convention *)
      if first then (
         (*
          * popl %ebp
          * popl %edi
          * popl %esi
          * popl %ebx
          * leave
          *)
         output_string o ("\t"^"popl"^"\t"^"%ebp"^"\n") ;
         output_string o ("\t"^"popl"^"\t"^"%edi"^"\n") ;
         output_string o ("\t"^"popl"^"\t"^"%esi"^"\n") ;
         output_string o ("\t"^"popl"^"\t"^"%ebx"^"\n") ;
         output_string o ("\t"^"leave"^"\n") 
      ) else ( (* if we're not in the "go" function, follow the L1 convention *)
         (*
          * movl %ebp, %esp
          * popl %ebp
          *)
         output_string o ("\t"^"movl"^"\t"^"%ebp, %esp"^"\n") ;
         output_string o ("\t"^"popl"^"\t"^"%ebp"^"\n")
      );
      (* ret *)
      output_string o ("\t"^"ret"^"\n")
   | PrintInstr(ps,tv) ->
      (* pushl tv *)
      output_string o ("\t"^"pushl"^"\t");
      compile_tval o tv;
      output_string o "\n";
      (* call print *)
      output_string o ("\t"^"call"^"\t"^"print"^"\n");
      (* addl $8, %esp *)
      output_string o ("\t"^"addl"^"\t"^"$4, %esp"^"\n")
   | PrintStrInstr(ps,tv) ->
      (* pushl tv *)
      output_string o ("\t"^"pushl"^"\t");
      compile_tval o tv;
      output_string o "\n";
      (* call print *)
      output_string o ("\t"^"call"^"\t"^"print_str"^"\n");
      (* addl $8, %esp *)
      output_string o ("\t"^"addl"^"\t"^"$4, %esp"^"\n")
   | AllocInstr(ps,tv1,tv2) ->
      (* pushl tv2 *)
      output_string o ("\t"^"pushl"^"\t");
      compile_tval o tv2;
      output_string o "\n";
      (* pushl tv1 *)
      output_string o ("\t"^"pushl"^"\t");
      compile_tval o tv1;
      output_string o "\n";
      (* call allocate *)
      output_string o ("\t"^"call"^"\t"^"allocate"^"\n");
      (* addl $8, %esp *)
      output_string o ("\t"^"addl"^"\t"^"$8, %esp"^"\n")
   | StringInstr(ps,id) ->
      let s = (get_symbol id) in
      let len = String.length s in
      let elen = Int64.add (Int64.mul (Int64.of_int len) 2L) 1L in
      let tv1 = IntTVal(ps,elen) in
      let tv2 = IntTVal(ps,Int64.of_int 1) in
      (* pushl tv2 *)
      output_string o ("\t"^"pushl"^"\t");
      compile_tval o tv2;
      output_string o "\n";
      (* pushl tv1 *)
      output_string o ("\t"^"pushl"^"\t");
      compile_tval o tv1;
      output_string o "\n";
      (* call allocate *)
      output_string o ("\t"^"call"^"\t"^"allocate"^"\n");
      (* addl $8, %esp *)
      output_string o ("\t"^"addl"^"\t"^"$8, %esp"^"\n");
      compile_strlit o s ps first j k
   | ArrayErrorInstr(ps,tv1,tv2) ->
      (* pushl tv2 *)
      output_string o ("\t"^"pushl"^"\t");
      compile_tval o tv2;
      output_string o "\n";
      (* pushl tv1 *)
      output_string o ("\t"^"pushl"^"\t");
      compile_tval o tv1;
      output_string o "\n";
      (* call print_error *)
      output_string o ("\t"^"call"^"\t"^"print_error"^"\n");
      (* addl $8, %esp *)
      output_string o ("\t"^"addl"^"\t"^"$8, %esp"^"\n")

(* compiles an L1 "x" nonterminal into x86 assembly *)
and compile_reg (o : out_channel) (r : reg) : unit = match r with
   | CallerSaveReg(ps,cr) -> compile_creg o cr
   | EsiReg(ps) -> output_string o "%esi"
   | EdiReg(ps) -> output_string o "%edi"
   | EbpReg(ps) -> output_string o "%ebp"
   | EspReg(ps) -> output_string o "%esp"

(* compiles an L1 "cx" nonterminal into x86 assembly *)
and compile_creg (o : out_channel) (cr : creg) : unit = match cr with
   | EaxReg(ps) -> output_string o "%eax"
   | EcxReg(ps) -> output_string o "%ecx"
   | EdxReg(ps) -> output_string o "%edx"
   | EbxReg(ps) -> output_string o "%ebx"

(* compiles an L1 "sx" nonterminal into x86 assembly *)
and compile_sreg (o : out_channel) (sr : sreg) : unit = match sr with
   | EcxShReg(ps) -> output_string o "%ecx"
   | IntShVal(ps,i) -> output_string o ("$"^(Int64.to_string i))

(* compiles an L1 "s" nonterminal into x86 assembly *)
and compile_sval (o : out_channel) (sv : sval) : unit = match sv with
   | RegSVal(ps,r) -> compile_reg o r;
   | IntSVal(ps,i) -> output_string o ("$"^(Int64.to_string i))
   | LabelSVal(ps,l) -> output_string o ("$_"^(get_symbol l))

(* compiles an L1 "u" nonterminal into x86 assembly *)
and compile_uval (o : out_channel) (uv : uval) : unit = match uv with
   | RegUVal(ps,r) -> output_string o "*"; compile_reg o r
   | IntUVal(ps,i) -> output_string o (Int64.to_string i)
   | LabelUVal(ps,l) -> output_string o ("_"^(get_symbol l))

(* compiles an L1 "t" nonterminal into x86 assembly *)
and compile_tval (o : out_channel) (t : tval) : unit = match t with
   | RegTVal(ps,r) -> compile_reg o r
   | IntTVal(ps,i) -> output_string o ("$"^(Int64.to_string i))
   | LabelTVal(ps,l) -> output_string o ("$_"^(get_symbol l))

(* compiles an L1 label l into x86 assembly *)
and compile_label (o : out_channel) (l : int) : unit = 
   output_string o ("_"^(get_symbol l)^":\n") ;
and compile_strlit (o : out_channel) (s : string) (p : pos) (first : bool) (j : int) (k : int) : unit =
   let cl = explode s in
   let _ = List.fold_left (fun k c -> 
      let v = encode_int (Char.code c) in
      let i = MemWriteInstr(p,CallerSaveReg(p,EaxReg(p)),Int64.of_int k,IntSVal(p,v)) in
      compile_instr o i first j k;
      (k + 4)
   ) 4 cl in ()
;;

(*
 * compile_and_link filename
 *
 * Issues the system calls for compile/link of the generated
 * C and assembly code.
 *
 * filename  - the filename of the output binary
 *
 * returns unit
 *)
let compile_and_link (filename : string) (assembly_file_name : string) (runtime_file_name : string) : unit =
   let r1c = ("as --32 -o "^assembly_file_name^".o "^assembly_file_name) in
   let r2c = ("gcc -m32 -c -O2 -o "^runtime_file_name^".o "^runtime_file_name) in
   let r3c = ("gcc -m32 -o "^filename^" "^assembly_file_name^".o "^runtime_file_name^".o") in
   let r1 = Sys.command (r1c^" 2> /dev/null")  in
   let r2 = Sys.command (r2c^" 2> /dev/null") in
   let r3 = Sys.command (r3c^" 2> /dev/null") in
   if (r1 <> 0) then die_system_error ("assembler failed: \""^r1c^"\" returned "^(string_of_int r1));
   if (r2 <> 0) then die_system_error ("compiler failed: \""^r2c^"\" returned "^(string_of_int r2));
   if (r3 <> 0) then die_system_error ("compiler/linker failed: \""^r3c^"\" returned "^(string_of_int r3));
   (* delete all the temporary files *)
   Unix.unlink assembly_file_name;
   Unix.unlink (assembly_file_name^".o");
   Unix.unlink runtime_file_name;
   Unix.unlink (runtime_file_name^".o");
;;

(*
 * generate_runtime o
 *
 * Generates the C runtime code on the specified output channel.
 * The runtime has the implementations of the "print", "allocate",
 * and "array-error" L1 functions.
 *
 * o - the output channel where the code gets written
 *
 * returns unit
 *)
let generate_runtime (o : out_channel) : unit =
   output_string o "#include <string.h>\n";
   output_string o "#include <stdlib.h>\n";
   output_string o "#include <stdio.h>\n";
   output_string o "\n";
   output_string o ("#define HEAP_SIZE "^(string_of_int !heap_size)^" // the heap size\n");
   output_string o "//#define HEAP_SIZE 1048576  // one megabyte\n";
   output_string o "//#define HEAP_SIZE 20       // small heap size for testing\n";
   output_string o ((if !gc_enabled then "" else "//")^"#define ENABLE_GC          // uncomment this to enable GC\n");
   output_string o ((if has_debug "gc" then "" else "//")^"#define GC_DEBUG           // uncomment this to enable GC debugging\n");
   output_string o "\n";
   output_string o "void **heap;      // the current heap\n";
   output_string o "void **heap2;     // the heap for copying\n";
   output_string o "void **heap_temp; // a pointer used for swapping heap/heap2\n";
   output_string o "\n";
   output_string o "int *allocptr;           // current allocation position\n";
   output_string o "int words_allocated = 0;\n";
   output_string o "\n";
   output_string o "int *stack; // pointer to the bottom of the stack (i.e. value\n";
   output_string o "            // upon program startup)\n";
   output_string o "\n";
   output_string o "/*\n";
   output_string o " * Helper for the print() function\n";
   output_string o " */\n";
   output_string o "void print_content(void **in, int depth) {\n";
   output_string o "   int i, x, size;\n";
   output_string o "   void **data;\n";
   output_string o "\n";
   output_string o "   if(depth >= 4) {\n";
   output_string o "      printf(\"...\");\n";
   output_string o "      return;\n";
   output_string o "   }\n";
   output_string o "   // NOTE: this function crashes quite messily if \"in\" is 0\n";
   output_string o "   // so we've added this check\n";
   output_string o "   if(in == NULL) {\n";
   output_string o "      printf(\"nil\");\n";
   output_string o "      return;\n";
   output_string o "   }\n";
   output_string o "   x = (int)in;\n";
   output_string o "   if(x & 1) {\n";
   output_string o "      printf(\"%i\", x >> 1);\n";
   output_string o "   } else {\n";
   output_string o "      size= *((int*)in);\n";
   output_string o "      data = in + 1;\n";
   output_string o "      printf(\"{s:%i\", size);\n";
   output_string o "      for(i = 0; i < size; i++) {\n";
   output_string o "         printf(\", \");\n";
   output_string o "         print_content(*data, depth + 1);\n";
   output_string o "         data++;\n";
   output_string o "      }\n";
   output_string o "      printf(\"}\");\n";
   output_string o "   }\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "\n";
   output_string o "/*\n";
   output_string o " * Runtime \"print\" function\n";
   output_string o " */\n";
   output_string o "int print(void *l) {\n";
   output_string o "   print_content(l, 0);\n";
   output_string o "   printf(\"\\n\");\n";
   output_string o "\n";
   output_string o "   return 1;\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "/*\n";
   output_string o " * Runtime function for printing an array as a string\n";
   output_string o " */\n";
   output_string o "void print_str(int **in) {\n";
   output_string o "   int i, x, size;\n";
   output_string o "   int **data;\n";
   output_string o "   int c;\n";
   output_string o "\n";
   output_string o "   if(in == NULL) {\n";
   output_string o "      printf(\"nil\");\n";
   output_string o "      return;\n";
   output_string o "   }\n";
   output_string o "   x = (int)in;\n";
   output_string o "   if(x & 1) {\n";
   output_string o "      printf(\"%i\\n\", x >> 1);\n";
   output_string o "   } else {\n";
   output_string o "      size= (int)(*in);\n";
   output_string o "      data = in + 1;\n";
   output_string o "      //fwrite(data,sizeof(char),size,stdout);\n";
   output_string o "      for(i = 0; i < size; i++) {\n";
   output_string o "         c = (int)data[i];\n";
   output_string o "         putchar(c >> 1);\n";
   output_string o "      }\n";
   output_string o "   }\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "/*\n";
   output_string o " * Helper for the gc() function.\n";
   output_string o " * Copies (compacts) an object from the old heap into\n";
   output_string o " * the empty heap\n";
   output_string o " */\n";
   output_string o "int *gc_copy(int *old)  {\n";
   output_string o "   int i, size;\n";
   output_string o "   int *old_array, *new_array, *first_array_location;\n";
   output_string o "\n";
   output_string o "   // If not a pointer or not a pointer to a heap location, return input value\n";
   output_string o "   if((int)old % 4 != 0 || (void**)old < heap2 || (void**)old >= heap2 + HEAP_SIZE) {\n";
   output_string o "       return old;\n";
   output_string o "   }\n";
   output_string o "\n";
   output_string o "   old_array = (int*)old;\n";
   output_string o "   size = old_array[0];\n";
   output_string o "\n";
   output_string o "   // If the size is negative, the array has already been copied to the\n";
   output_string o "   // new heap, so the first location of array will contain the new address\n";
   output_string o "   if(size == -1) {\n";
   output_string o "       return (int*)old_array[1];\n";
   output_string o "   }\n";
   output_string o "\n";
   output_string o "   // Mark the old array as invalid, create the new array\n";
   output_string o "   old_array[0] = -1;\n";
   output_string o "   new_array = allocptr;\n";
   output_string o "   allocptr += (size + 1);\n";
   output_string o "   words_allocated += (size + 1);\n";
   output_string o "\n";
   output_string o "   // The value of old_array[1] needs to be handled specially\n";
   output_string o "   // since it holds a pointer to the new heap object\n";
   output_string o "   first_array_location = (int*)old_array[1];\n";
   output_string o "   old_array[1] = (int)new_array;\n";
   output_string o "\n";
   output_string o "   // Set the values of new_array handling the first two locations separately\n";
   output_string o "   new_array[0] = size;\n";
   output_string o "   new_array[1] = (int)gc_copy(first_array_location);\n";
   output_string o "\n";
   output_string o "   // Call gc_copy on the remaining values of the array\n";
   output_string o "   for (i = 2; i <= size; i++) {\n";
   output_string o "      new_array[i] = (int)gc_copy((int*)old_array[i]);\n";
   output_string o "   }\n";
   output_string o "\n";
   output_string o "   return new_array;\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "/*\n";
   output_string o " * Initiates garbage collection\n";
   output_string o " */\n";
   output_string o "void gc(int *esp) {\n";
   output_string o "   int i;\n";
   output_string o "   int stack_size = stack - esp + 1;       // calculate the stack size\n";
   output_string o "   int prev_words_alloc = words_allocated;\n";
   output_string o "\n";
   output_string o "#ifdef GC_DEBUG\n";
   output_string o "   printf(\"GC: stack=(%p,%p) (size %d): \", esp, stack, stack_size);\n";
   output_string o "#endif\n";
   output_string o "\n";
   output_string o "   // swap in the empty heap to use for storing\n";
   output_string o "   // compacted objects\n";
   output_string o "   heap_temp = heap;\n";
   output_string o "   heap = heap2;\n";
   output_string o "   heap2 = heap_temp;\n";
   output_string o "\n";
   output_string o "   // reset heap position\n";
   output_string o "   allocptr = (int*)heap;\n";
   output_string o "   words_allocated = 0;\n";
   output_string o "\n";
   output_string o "   // NOTE: the edi/esi register contents could also be\n";
   output_string o "   // roots, but these have been placed in the stack\n";
   output_string o "   // by the allocate() assembly function.  Thus,\n";
   output_string o "   // we only need to look at the stack at this point\n";
   output_string o "\n";
   output_string o "   // Then, we need to copy anything pointed at\n";
   output_string o "   // by the stack into our empty heap\n";
   output_string o "   for(i = 0; i < stack_size; i++) {\n";
   output_string o "      esp[i] = (int)gc_copy((int*)esp[i]);\n";
   output_string o "   }\n";
   output_string o "\n";
   output_string o "#ifdef GC_DEBUG\n";
   output_string o "   printf(\"reclaimed %d words\\n\", (prev_words_alloc - words_allocated));\n";
   output_string o "#endif\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "/*\n";
   output_string o " * The \"allocate\" runtime function\n";
   output_string o " * (assembly stub that calls the 3-argument\n";
   output_string o " * allocate_helper function)\n";
   output_string o " */\n";
   output_string o "extern void* allocate(int fw_size, void *fw_fill);\n";
   output_string o "asm(\n";
   output_string o "   \".globl allocate\\n\"\n";
   output_string o "   \".type allocate, @function\\n\"\n";
   output_string o "   \"allocate:\\n\"\n";
   output_string o "   \"# grab the arguments (into eax,edx)\\n\"\n";
   output_string o "   \"popl %ecx\\n\" // return val\n";
   output_string o "   \"popl %eax\\n\" // arg 1\n";
   output_string o "   \"popl %edx\\n\" // arg 2\n";
   output_string o "   \"# put the original edi/esi on stack instead of args\\n\"\n";
   output_string o "   \"pushl %edi\\n\" // formerly edx\n";
   output_string o "   \"pushl %esi\\n\" // formerly eax\n";
   output_string o "   \"pushl %ebx\\n\" // formerly return addr  <-- this is the ESP we want\n";
   output_string o "   \"pushl %ecx\\n\" // ecx (return val)\n";
   output_string o "   \"pushl %eax\\n\" // eax (arg 1)\n";
   output_string o "   \"pushl %edx\\n\" // edx (arg 2)\n";
   output_string o "   \"# save the original esp (into ecx)\\n\"\n";
   output_string o "   \"movl %esp, %ecx\\n\"\n";
   output_string o "   \"addl $12, %ecx\\n\"\n";
   output_string o "   \"\\n\"\n";
   output_string o "   \"# save the caller's base pointer (so that LEAVE works)\\n\"\n";
   output_string o "   \"# body begins with base and\\n\"\n";
   output_string o "   \"# stack pointers equal\\n\"\n";
   output_string o "   \"pushl %ebp\\n\"\n";
   output_string o "   \"movl %esp, %ebp\\n\"\n";
   output_string o "   \"# push the first three args on stack\\n\"\n";
   output_string o "   \"pushl %ecx\\n\"\n";
   output_string o "   \"pushl %edx\\n\"\n";
   output_string o "   \"pushl %eax\\n\"\n";
   output_string o "   \"# call the real alloc\\n\"\n";
   output_string o "   \"call allocate_helper\\n\"\n";
   output_string o "   \"addl $12, %esp\\n\"\n";
   output_string o "   \"\\n\"\n";
   output_string o "   \"# restore the original base pointer (from stack)\\n\"\n";
   output_string o "   \"leave\\n\"\n";
   output_string o "   \"# restore esi/edi from stack\\n\"\n";
   output_string o "   \"popl %edx\\n\"  // arg 2\n";
   output_string o "   \"popl %ecx\\n\"  // arg 1\n";
   output_string o "   \"addl $4, %esp\\n\" // skip over return val (it hasn't changed)\n";
   output_string o "   \"popl %ebx\\n\"  // restore ebx\n";
   output_string o "   \"popl %esi\\n\"  // restore esi\n";
   output_string o "   \"popl %edi\\n\"  // restore edi\n";
   output_string o "   \"pushl %edx\\n\" // put back arg 2\n";
   output_string o "   \"pushl %ecx\\n\" // put back arg 1\n";
   output_string o "   \"subl $8, %esp\\n\" // skip over old ebx\n";
   output_string o "   \"popl %edx\\n\"  // original return addr\n";
   output_string o "   \"popl %ecx\\n\"  // junk\n";
   output_string o "   \"pushl %edx\\n\"  // restore return addr\n";
   output_string o "   \"ret\\n\" \n";
   output_string o ");\n";
   output_string o "\n";
   output_string o "/*\n";
   output_string o " * The real \"allocate\" runtime function\n";
   output_string o " * (called by the above assembly stub function)\n";
   output_string o " */\n";
   output_string o "void* allocate_helper(int fw_size, void *fw_fill, int *esp)\n";
   output_string o "{\n";
   output_string o "   int i, data_size, array_size;\n";
   output_string o "   int *ret;\n";
   output_string o "\n";
   output_string o "#ifdef GC_DEBUG\n";
   output_string o "   printf(\"runtime.c: allocate(): ESP = %p (%d), EDI = %p (%d), ESI = %p (%d), EBX = %p (%d)\\n\",\n";
   output_string o "          esp, (int)esp, (int*)esp[2], esp[2], (int*)esp[1], esp[1], (int*)esp[0], esp[0]);\n";
   output_string o "#endif\n";
   output_string o "\n";
   output_string o "   if(!(fw_size & 1)) {\n";
   output_string o "      printf(\"allocate called with size input that was not an encoded integer, %i\\n\",\n";
   output_string o "             fw_size);\n";
   output_string o "      exit(-1);\n";
   output_string o "   }\n";
   output_string o "\n";
   output_string o "   data_size = fw_size >> 1;\n";
   output_string o "\n";
   output_string o "   if(data_size < 0) {\n";
   output_string o "      printf(\"allocate called with size of %i\\n\", data_size);\n";
   output_string o "      exit(-1);\n";
   output_string o "   }\n";
   output_string o "\n";
   output_string o "   // Even if there is no data, allocate an array of two words\n";
   output_string o "   // so we can hold a forwarding pointer and an int representing if\n";
   output_string o "   // the array has already been garbage collected\n";
   output_string o "   array_size = (data_size == 0) ? 2 : data_size + 1;\n";
   output_string o "\n";
   output_string o "   // Check if the heap has space for the allocation\n";
   output_string o "   if(words_allocated + data_size >= HEAP_SIZE)\n";
   output_string o "   {\n";
   output_string o "#ifdef ENABLE_GC\n";
   output_string o "      // Garbage collect\n";
   output_string o "      gc(esp);\n";
   output_string o "\n";
   output_string o "      // Check if the garbage collection free enough space for the allocation\n";
   output_string o "      if(words_allocated + data_size >= HEAP_SIZE) {\n";
   output_string o "#endif\n";
   output_string o "         printf(\"out of memory\\n\"); // NOTE: we've added a newline\n";
   output_string o "         exit(-1);\n";
   output_string o "#ifdef ENABLE_GC\n";
   output_string o "      }\n";
   output_string o "#endif\n";
   output_string o "   }\n";
   output_string o "\n";
   output_string o "   // Do the allocation\n";
   output_string o "   ret = allocptr;\n";
   output_string o "   allocptr += array_size;\n";
   output_string o "   words_allocated += array_size;\n";
   output_string o "\n";
   output_string o "   // Set the size of the array to be the desired size\n";
   output_string o "   ret[0] = data_size;\n";
   output_string o "\n";
   output_string o "   // If there is no data, set the value of the array to be a number\n";
   output_string o "   // so it can be properly garbage collected\n";
   output_string o "   if(data_size == 0) {\n";
   output_string o "      ret[1] = 1;\n";
   output_string o "   } else {\n";
   output_string o "      // Fill the array with the fill value\n";
   output_string o "      for(i = 0; i < data_size; i++) {\n";
   output_string o "         ret[i+1] = (int)fw_fill;\n";
   output_string o "      }\n";
   output_string o "   }\n";
   output_string o "\n";
   output_string o "   return ret;\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "/*\n";
   output_string o " * The \"print-error\" runtime function\n";
   output_string o " */\n";
   output_string o "int print_error(int *array, int fw_x) {\n";
   output_string o "   printf(\"attempted to use position %i in an array that only has %i positions\\n\",\n";
   output_string o "          fw_x >> 1, *array);\n";
   output_string o "   exit(0);\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "/*\n";
   output_string o " * Program entry-point\n";
   output_string o " */\n";
   output_string o "int main() {\n";
   output_string o "   heap  = (void*)malloc(HEAP_SIZE * sizeof(void*));\n";
   output_string o "   heap2 = (void*)malloc(HEAP_SIZE * sizeof(void*));\n";
   output_string o "   allocptr = (int*)heap;\n";
   output_string o "   // NOTE: allocptr needs to appear in the following check, because otherwise\n";
   output_string o "   // gcc apparently optimizes away the assignment (i.e. the allocate_helper function\n";
   output_string o "   // sees allocptr as NULL)\n";
   output_string o "   if(!allocptr || !heap2) {\n";
   output_string o "      printf(\"malloc failed\\n\");\n";
   output_string o "      exit(-1);\n";
   output_string o "   }\n";
   output_string o "\n";
   output_string o "   // Move esp into the bottom-of-stack pointer.\n";
   output_string o "   // The \"go\" function's boilerplate (as long as one copies it\n";
   output_string o "   // correctly from the lecture notes), in conjunction with\n";
   output_string o "   // the C calling convention dictates that there will be\n";
   output_string o "   // exactly 6 words added to the stack before the\n";
   output_string o "   // body of \"go\" actually happens\n";
   output_string o "   asm (\"movl %%esp, %%eax;\"\n";
   output_string o "        \"subl $24, %%eax;\" // 6 * 4\n";
   output_string o "        \"movl %%eax, %0;\"\n";
   output_string o "        \"call go;\"\n";
   output_string o "      : \"=m\"(stack) // outputs\n";
   output_string o "      :             // inputs (none)\n";
   output_string o "      : \"%eax\"      // clobbered registers (eax)\n";
   output_string o "   );  \n";
   output_string o "\n";
   output_string o "#ifdef GC_DEBUG\n";
   output_string o "   printf(\"runtime.c: main(): initial ESP value = %p (%d)\\n\", stack, (int)stack);\n";
   output_string o "#endif\n";
   output_string o "\n";
   output_string o "   return 0;\n";
   output_string o "}\n";
;;

(* this dumps the binary, given a program AST *)
let generate_binary (result : program) (output_file_name : string) : unit = 
   let runtime_file_name = (Filename.temp_file ?temp_dir:(Some("")) "runtime_" ".c") in
   let assembly_file_name = (Filename.temp_file ?temp_dir:(Some("")) "prog_" ".S") in
   (* generate the C runtime *)
   let out1 = (try (open_out runtime_file_name)
      with _ -> die_system_error ("can't write to file: "^
         (Sys.getcwd ())^"/"^(runtime_file_name))
   ) in
   generate_runtime out1;
   close_out out1;
   (* generate the assembly code *)
   let out2 = (try (open_out assembly_file_name)
      with _ -> die_system_error ("can't write to file: "^
      (Sys.getcwd ())^"/"^(assembly_file_name))
   ) in
   compile_program out2 result;
   close_out out2;
   (* compile and link everything *)
   compile_and_link output_file_name assembly_file_name runtime_file_name
;;
