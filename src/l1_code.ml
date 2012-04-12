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

open L1_ast;;
open Utils;;

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
        | Some(s) -> ("_"^s))) in
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
      output_string o s;
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
         output_string o s1;
         output_string o "\n";
         (* jmp s2 *)
         output_string o ("\t"^"jmp"^"\t"^"_");
         output_string o s2;
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
         output_string o s1;
         output_string o "\n";
         (* jmp s2 *)
         output_string o ("\t"^"jmp"^"\t"^"_");
         output_string o s2;
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
         output_string o s1;
         output_string o "\n";
         (* jmp s2 *)
         output_string o ("\t"^"jmp"^"\t"^"_");
         output_string o s2;
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
   | LabelSVal(ps,l) -> output_string o ("$_"^l)

(* compiles an L1 "u" nonterminal into x86 assembly *)
and compile_uval (o : out_channel) (uv : uval) : unit = match uv with
   | RegUVal(ps,r) -> output_string o "*"; compile_reg o r
   | IntUVal(ps,i) -> output_string o (Int64.to_string i)
   | LabelUVal(ps,l) -> output_string o ("_"^l)

(* compiles an L1 "t" nonterminal into x86 assembly *)
and compile_tval (o : out_channel) (t : tval) : unit = match t with
   | RegTVal(ps,r) -> compile_reg o r
   | IntTVal(ps,i) -> output_string o ("$"^(Int64.to_string i))
   | LabelTVal(ps,l) -> output_string o ("$_"^l)

(* compiles an L1 label l into x86 assembly *)
and compile_label (o : out_channel) (l : string) : unit = 
   output_string o ("_"^l^":\n") ;
;;

(*
 * compile_and_link filename use_32bit
 *
 * Issues the system calls for compile/link of the generated
 * C and assembly code.
 *
 * filename  - the filename of the output binary
 * use_32bit - whether to generate a 32bit binary (rather than 64bit)
 *
 * returns unit
 *)
let compile_and_link (filename : string) (use_32bit : bool) : unit =
   let arch = if use_32bit then 32 else 64 in
   let r1c = ("as --"^(string_of_int arch)^" -o prog.o prog.S") in
   let r2c = ("gcc -m"^(string_of_int arch)^" -c -O2 -o runtime.o runtime.c") in
   let r3c = ("gcc -m"^(string_of_int arch)^" -o "^filename^" prog.o runtime.o") in
   let r1 = Sys.command (r1c^" 2> /dev/null")  in
   let r2 = Sys.command (r2c^" 2> /dev/null") in
   let r3 = Sys.command (r3c^" 2> /dev/null") in
   if (r1 <> 0) then die_system_error ("assembler failed: \""^r1c^"\" returned "^(string_of_int r1));
   if (r2 <> 0) then die_system_error ("compiler failed: \""^r2c^"\" returned "^(string_of_int r2));
   if (r3 <> 0) then die_system_error ("compiler/linker failed: \""^r3c^"\" returned "^(string_of_int r3));
   ()
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
   output_string o "void print_content(void** in, int depth) {\n";
   output_string o "  if (depth >= 4) {\n";
   output_string o "    printf(\"...\");\n";
   output_string o "    return;\n";
   output_string o "  }\n";
   output_string o "  int x = (int) in;\n";
   output_string o "  if (x&1) {\n";
   output_string o "    printf(\"%i\",x>>1);\n";
   output_string o "  } else {\n";
   output_string o "    int size= *((int*)in);\n";
   output_string o "    void** data = in+1;\n";
   output_string o "    int i;\n";
   output_string o "    printf(\"{s:%i\", size);\n";
   output_string o "    for (i=0;i<size;i++) {\n";
   output_string o "      printf(\", \");\n";
   output_string o "      print_content(*data,depth+1);\n";
   output_string o "      data++;\n";
   output_string o "    }\n";
   output_string o "    printf(\"}\");\n";
   output_string o "  }\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "int print(void* l) {\n";
   output_string o "  print_content(l,0);\n";
   output_string o "  printf(\"\\n\");\n";
   output_string o "  return 1;\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "#define HEAP_SIZE 1048576  // one megabyte\n";
   output_string o "\n";
   output_string o "void** heap;\n";
   output_string o "void** allocptr;\n";
   output_string o "int words_allocated=0;\n";
   output_string o "\n";
   output_string o "void* allocate(int fw_size, void *fw_fill) {\n";
   output_string o "  int size = fw_size >> 1;\n";
   output_string o "  void** ret = (void**)allocptr;\n";
   output_string o "  int i;\n";
   output_string o "\n";
   output_string o "  if (!(fw_size&1)) {\n";
   output_string o "    printf(\"allocate called with size input that was not an encoded integer, %i\\n\",\n";
   output_string o "           fw_size);\n";
   output_string o "  }\n";
   output_string o "  if (size < 0) {\n";
   output_string o "    printf(\"allocate called with size of %i\\n\",size);\n";
   output_string o "    exit(-1);\n";
   output_string o "  }\n";
   output_string o "\n";
   output_string o "  allocptr+=(size+1);\n";
   output_string o "  words_allocated+=(size+1);\n";
   output_string o "  \n";
   output_string o "  if (words_allocated < HEAP_SIZE) {\n";
   output_string o "    *((int*)ret)=size;\n";
   output_string o "    void** data = ret+1;\n";
   output_string o "    for (i=0;i<size;i++) {\n";
   output_string o "      *data = fw_fill;\n";
   output_string o "      data++;\n";
   output_string o "    }\n";
   output_string o "    return ret;\n";
   output_string o "  }\n";
   output_string o "  else {\n";
   output_string o "    printf(\"out of memory\");\n";
   output_string o "    exit(-1);\n";
   output_string o "  }\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "int print_error(int* array, int fw_x) {\n";
   output_string o "  printf(\"attempted to use position %i in an array that only has %i positions\\n\",\n";
   output_string o "		 fw_x>>1, *array);\n";
   output_string o "  exit(0);\n";
   output_string o "}\n";
   output_string o "\n";
   output_string o "int main() {\n";
   output_string o "  heap=(void*)malloc(HEAP_SIZE*sizeof(void*));\n";
   output_string o "  if (!heap) {\n";
   output_string o "    printf(\"malloc failed\\n\");\n";
   output_string o "    exit(-1);\n";
   output_string o "  }\n";
   output_string o "  allocptr=heap;\n";
   output_string o "  go();   // call into the generated code\n";
   output_string o " return 0;\n";
   output_string o "}\n";
;;
