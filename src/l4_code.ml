(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/14/2012
 *
 * L4-to-L3 Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * l4_code.ml
 * Contains the l4-to-l3 compilation
 * functionality.
 *)

open L4_ast;;
open Utils;;

(*********************************************************
 **  L4-to-L3 CODE GENERATION                           **
 *********************************************************)

(* compile an L4 program into an L3 program *)

let rec compile_program (pr : L4_ast.program) : L3_ast.program =
   match pr with
   | Program(p,_,_) -> L3_ast.Program(p,L3_ast.DExpExp(p,L3_ast.SValDExp(p,L3_ast.LabelSVal(p,""))),[])
;;
