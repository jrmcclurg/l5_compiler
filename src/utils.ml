(*
 * EECS 322 Compiler Construction
 * Northwestern University
 * 4/3/2012
 *
 * L1-to-assembly Compiler
 * Jedidiah R. McClurg
 * v. 1.0
 *
 * utils.ml
 * Various utilities for parsing, printing error messages, etc.
 *)

open Lexing;;
open Parsing;;
open Ast;;

exception Parse_error;;

let max_int = 2147483647L ;;
let min_int = -2147483648L ;;

(* die_error p s
 *
 * Print error message and exit
 *
 * p - the location of the error
 * s - the error message
 *
 * returns unit
 *)
let die_error (p : pos) (s : string) =
   print_string "Parse error";
   print_string (match p with
   | NoPos -> ""
   | Pos(file_name,line_num,col_num) -> (" in '"^file_name^
    "' on line "^(string_of_int line_num)^" col "^(string_of_int
    col_num))
   );
   print_string (": "^s^"\n");
   exit 1
;;

(* dies with a parse error s *)
let parse_error (s : string) = 
   let p         = symbol_end_pos ()  in
   let file_name = p.Lexing.pos_fname in
   let line_num  = p.Lexing.pos_lnum  in
   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
   let ps        = Pos(file_name,line_num,col_num) in
   die_error ps s
;;

(* dies with a system error s *)
let die_system_error (s : string) =
   print_string s;
   print_string "\n";
   exit 1
;;

(* gets a pos data structure using the current lexing pos *)
let get_current_pos () =
   let p         = symbol_start_pos () in
   let file_name = p.Lexing.pos_fname  in
   let line_num  = p.Lexing.pos_lnum   in
   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
   Pos(file_name,line_num,col_num)
;;

(* gets a pos data structure from a lexing position *)
let get_pos (p : Lexing.position) =
   let file_name = p.Lexing.pos_fname in
   let line_num  = p.Lexing.pos_lnum  in
   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
   Pos(file_name,line_num,col_num)
;;

exception Lexing_error;;

(* updates the lexer position to the next line
 * (this is used since we skip newlines in the
 *  lexer, but we still wish to remember them
 *  for proper line positions) *)
let do_newline lb = 
   Lexing.new_line lb
;;

(* "casts" a reg to a creg *)
let get_creg r = match r with
   | CallerSaveReg(_,c) -> c
   | _ -> parse_error "destination must be one of eax, ecx, edx, ebx"
;;

(* does an integer range check *)
let check_int_range (i : int64) =
   if ((i < min_int) or (i > max_int)) then parse_error "integer out of range"
;;
