open Ast;;
open Utils;;

let rec compile_program (o : out_channel) (p : program) = match p with
   | Program(ps, fl) ->
      (*output_string o ".global go\n";
      output_string o "go:\n";
      output_string o "# the code goes here\n";
      output_string o "#   movl $5, %edi\n";
      output_string o "   pushl $5\n";
      output_string o "   call print\n";
      output_string o "   addl $4, %esp\n";
      output_string o "   ret\n";
      output_string o "# the code goes here\n";*)
      output_string o "	.file	\"prog.c\"\n" ;
      output_string o "	.text\n" ;
      output_string o "########## begin code ##########\n";
      output_string o "go:\n" ;
      output_string o "\n";
      let _ = List.fold_left (fun flag f ->
         compile_function o f flag;
         output_string o "\n";
         false
      ) true fl in ();
      output_string o "########## end code ##########\n";
      output_string o "	.ident	\"GCC: (Ubuntu 4.3.2-1ubuntu12) 4.3.2\"\n" ;
      output_string o "	.section	.note.GNU-stack,\"\",@progbits\n" ;

and compile_function (o : out_channel) (f : func) (first : bool) = match f with
   | Function(ps, so, il) ->
      let name = (if first then "go" else (match so with
        | None -> die_error ps "function must be named"
        | Some(s) -> ("_"^s))) in
      output_string o ("	.globl	"^name^"\n") ;
      output_string o ("	.type	"^name^", @function\n") ;
      output_string o ("########## begin function \""^name^"\" ##########\n");
      output_string o (name^":\n") ;
      (* if the "go" function (i.e. the first one) had a label, just print it *)
      if first then (match so with
      | None -> () 
      | Some(l) -> compile_label o l);
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
      output_string o "        ##### begin function body #####\n" ;
      List.iter (fun i ->
         compile_instr o i
      ) il;
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
      output_string o "        ret\n" ;
      output_string o ("########## end function \""^name^"\" ##########\n");
      output_string o ("	.size	"^name^", .-"^name^"\n") 

and compile_instr (o : out_channel) (i : instr) = match i with
   | PrintInstr(ps,tv) ->
      output_string o "\t# ";
      output_instr o i;
      output_string o "\n";
      output_string o "\tpushl\t";
      compile_tval o tv;
      output_string o "\n";
      output_string o "\tcall\tprint\n";
      output_string o "\taddl\t$4,%esp\n"
   | _ -> output_string o "\t### TODO XXX - unhandled instruction ###\n"

and compile_tval (o : out_channel) (t : tval) = match t with
   | RegTVal(ps,r) -> compile_reg o r
   | IntTVal(ps,i) -> output_string o ("$"^(string_of_int i))

and compile_reg (o : out_channel) (r : reg) = match r with
   | EsiReg(ps) -> output_string o "%esi"
   | EdiReg(ps) -> output_string o "%edi"
   | EbpReg(ps) -> output_string o "%ebp"
   | EspReg(ps) -> output_string o "%esp"
   | CallerSaveReg(ps,cr) -> compile_creg o cr

and compile_creg (o : out_channel) (cr : creg) = match cr with
   | EaxReg(ps) -> output_string o "%eax"
   | EcxReg(ps) -> output_string o "%ecx"
   | EdxReg(ps) -> output_string o "%edx"
   | EbxReg(ps) -> output_string o "%ebx"

and compile_label (o : out_channel) (l : string) = 
   output_string o ("_"^l^":\n") ;
;;

let compile_assembly () =
   let _ = Sys.command "as --32 -o prog.o prog.S" in
   let _ = Sys.command "gcc -m32 -c -O2 -w -o runtime.o runtime.c" in
   let _ = Sys.command "gcc -m32 -o a.out prog.o runtime.o" in
   ()
;;

let generate_runtime (o : out_channel) =
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
