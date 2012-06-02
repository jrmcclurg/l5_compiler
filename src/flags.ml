(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 5/23/2012
 *
 * Lc Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * flags.ml
 * Utilities for the command-line arguments
 *)

module StringSet = Set.Make(String);;

type spill_mode_type = SpillMin
                     | SpillMax
                     | SpillDampedDiff
                     | SpillIncrease
                     | SpillHalve of int
;;

(* defaults for command-line args *)
let heap_size        = ref 1048576;;                (* one megabyte *)
let spill_mode       = ref SpillIncrease;;          (* increase mode *)
let filename         = ref (None : string option);; (* stdin *)
let out_file_name    = ref (None : string option);;
let binary_file_name = ref "a.out";;
let target_lang      = ref 0;;                      (* compile to binary *)
let gc_enabled       = ref true;;                   (* runtime GC enabled *)

let debug_table = ref (StringSet.empty : StringSet.t);;

let add_debug (d : string) : unit =
   debug_table := StringSet.add d !debug_table
;;

let has_debug (d : string) : bool =
   StringSet.mem d !debug_table
;;

(* parse the command-line arguments *)
let args = Arg.align [
   ("-spill",    Arg.String(fun x -> match x with
                    | "min" -> spill_mode := SpillMin
                    | "max" -> spill_mode := SpillMax
                    | "diff" -> spill_mode := SpillDampedDiff
                    | "halve" -> spill_mode := SpillHalve(3)
                    | "halve2" -> spill_mode := SpillHalve(2)
                    | "halve3" -> spill_mode := SpillHalve(3)
                    | "halve4" -> spill_mode := SpillHalve(4)
                    | "halve5" -> spill_mode := SpillHalve(5)
                    | "halve6" -> spill_mode := SpillHalve(6)
                    | "halve7" -> spill_mode := SpillHalve(7)
                    | "halve8" -> spill_mode := SpillHalve(8)
                    | "halve9" -> spill_mode := SpillHalve(9)
                    | "inc" -> spill_mode := SpillIncrease
                    | _ -> spill_mode := SpillHalve(3)
                 ),
                    "<mode> Spill mode (max, inc, diff, min)");
   ("-debug",    Arg.String(fun x -> add_debug x),
                    "<flag> Add a debug flag (1, 2, 3, 4, 5, gc, spill, regs)");
   ("-heap",     Arg.Int(fun x -> heap_size := x),
                    "<size> Set the heap size in bytes (default 1048576)");
   ("-nogc",     Arg.Unit(fun x -> gc_enabled := false),
                    " Turn off runtime garbage collection");
   ("-target",   Arg.Int(fun x -> target_lang := x),
                    "<k> Set the target language to Lk (default to n-1)");
   ("-o",        Arg.String(fun x -> out_file_name := Some(x); binary_file_name := x),
                    "<file> Location of the result");
];;
