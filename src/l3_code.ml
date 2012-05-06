(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/7/2012
 *
 * L3-to-L2 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l3_code.ml
 * Contains the l3-to-l2 compilation
 * functionality.
 *)

open L3_ast;;
open Utils;;

(*********************************************************
 **  L3-to-L2 CODE GENERATION                           **
 *********************************************************)

(* compile an L2 program into an L1 program *)
(*
let rec compile_program (p : L2_ast.program) : L1_ast.program =
   match p with
   | Program(p,fl) -> 
      (* compile all the functions into L1 functions, giving
       * each one a unique count (starting with 0) *)
      let (_,fl2) = List.fold_left (fun (count,res) f ->
         (count+1,res@[compile_func f count])
      ) (0,[]) fl in
      L1_ast.Program(p, fl2)
*)
