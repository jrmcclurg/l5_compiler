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
let emit_asm         = ref false;;
let emit_runtime     = ref false;;
let verbose_mode     = ref false;;
let clear_uninit     = ref true;;

(* debug modes *)
let debug_1     = ref false;;
let debug_2     = ref false;;
let debug_3     = ref false;;
let debug_4     = ref false;;
let debug_5     = ref false;;
let debug_gc    = ref false;;
let debug_gdb   = ref false;;
let debug_spill = ref false;;
let debug_stats = ref false;;

let error_and_exit s =
   output_string stderr ("Error: "^s^"\n");
   exit 1
;;

(* parse the command-line arguments *)
let verbose_fun = (fun x -> 
   verbose_mode := true;
   debug_1 := false; debug_2 := false; debug_3 := false; debug_4 := false;
   debug_5 := false; debug_gc := false; debug_spill := false; debug_stats := false;
   debug_gdb := false
);;
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
                    | _ -> error_and_exit "invalid spill mode"
                 ),
                    "<mode> Spill mode (max, inc, halve<k>, diff, min) (default halve3)");
   ("-v",        Arg.Unit(verbose_fun),
                    " Turn on verbose output");
   ("-verbose",  Arg.Unit(verbose_fun),
                    " Turn on verbose output");
   ("-debug",    Arg.String(fun x ->
                            verbose_mode := false;
                            match x with
                            | "1" -> debug_1 := true
                            | "2" -> debug_2 := true
                            | "3" -> debug_3 := true
                            | "4" -> debug_4 := true
                            | "5" -> debug_5 := true
                            | "gc" -> debug_gc := true
                            | "gdb" -> debug_gdb := true
                            | "spill" -> debug_spill := true
                            | "stats" -> debug_stats := true
                            | "all" ->
                               debug_1 := true; debug_2 := true; debug_3 := true; debug_4 := true;
                               debug_5 := true; debug_gc := true; debug_spill := true; debug_stats := true;
                               debug_gdb := true
                            | _ -> error_and_exit "invalid debug mode"
                            ),
                    "<flag> Add a debug flag (1, 2, 3, 4, 5, gc, gdb, spill, stats)");
   ("-heap",     Arg.Int(fun x -> heap_size := x),
                    "<size> Set the heap size in bytes (default 1048576)");
   ("-nogc",     Arg.Unit(fun x -> gc_enabled := false),
                    " Turn off runtime garbage collection");
   ("-noclear",  Arg.Unit(fun x -> clear_uninit := false),
                    " Turn off clearing of stack/callee-saves (may impede GC performance)");
   ("-runtime",  Arg.Unit(fun x -> emit_runtime := true),
                    " Emit the C runtime");
   ("-asm",      Arg.Unit(fun x -> emit_asm := true),
                    " Emit the generated assembly code");
   ("-target",   Arg.Int(fun x -> target_lang := x),
                    "<k> Set the target language to Lk (default to n-1)");
   ("-o",        Arg.String(fun x -> out_file_name := Some(x); binary_file_name := x),
                    "<file> Location of the result");
];;
