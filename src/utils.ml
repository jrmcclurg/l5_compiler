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

(* data type for file positions *)
type pos = NoPos | Pos of string*int*int;; (* file,line,col *)

exception Parse_error;;
exception Lexing_error;;

(* do_error p s
 *
 * Print error message
 *
 * p - the location of the error
 * s - the error message
 *
 * returns unit
 *)
let do_error (p : pos) (s : string) : unit =
   print_string "Error";
   print_string (match p with
   | NoPos -> ""
   | Pos(file_name,line_num,col_num) -> (" in '"^file_name^
    "' on line "^(string_of_int line_num)^" col "^(string_of_int
    col_num))
   );
   print_string (": "^s^"\n")
;;

let die_error (p : pos) (s : string) =
   do_error p s;
   exit 1;
;;

(* dies with a general position-based error *)
let pos_error (s : string) (p : position) = 
   let file_name = p.Lexing.pos_fname in
   let line_num  = p.Lexing.pos_lnum  in
   let col_num   = (p.Lexing.pos_cnum-p.Lexing.pos_bol+1) in
   let ps        = Pos(file_name,line_num,col_num) in
   do_error ps s
;;

(* dies with a parse error s *)
let parse_error (s : string) = 
   pos_error s (symbol_end_pos ());
   raise Parse_error
;;

(* dies with a lexing error *)
let lex_error (s : string) (lexbuf : Lexing.lexbuf) = 
   pos_error s (Lexing.lexeme_end_p lexbuf);
   raise Lexing_error
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

(* updates the lexer position to the next line
 * (this is used since we skip newlines in the
 *  lexer, but we still wish to remember them
 *  for proper line positions) *)
let do_newline lb = 
   Lexing.new_line lb
;;

(* dies with a system error s *)
let die_system_error (s : string) =
   print_string s;
   print_string "\n";
   exit 1
;;

let max_int = 2147483647L ;;
let min_int = -2147483648L ;;

(* does an integer range check *)
let check_int_range (i : int64) =
   if ((i < min_int) or (i > max_int)) then parse_error "integer out of range"
;;

(* does a check to see if integer is divisible by 4 *)
let check_int_alignment (i : int64) =
   if ((Int64.rem i 4L) <> 0L) then parse_error "offset must be divisible by 4"
;;

let prefix_chr = "0";;
let unique_counter = ref 0;;
let max_prefix = ref "";;

let rec update_max_ident (s : string) : unit =
   if (String.length s >= String.length (!max_prefix)) then (
      max_prefix := (!max_prefix^prefix_chr);
      update_max_ident s
   )
;;

let get_unique_ident (prefix : string) : string =
   let result = (prefix^(!max_prefix)^(string_of_int !unique_counter)) in
   if !unique_counter >= Pervasives.max_int then (
      (* if we have run out of unique integers, wrap back to zero
       * and increase the length of the alphabetical part of the prefix *)
      unique_counter := 0;
      max_prefix := (!max_prefix^prefix_chr)
   ) else (
     unique_counter := (!unique_counter + 1)
   );
   result
;;

let make_ident_unique (prefix : string) (s : string) : string =
   (prefix^s^(!max_prefix))
;;

let unique_id = ref 1;; (* 0 is reserved for "NULL" *)
let symbol_table = ((Hashtbl.create 64) : (string,int) Hashtbl.t);;
let max_symbol_len = ref 0;;

let get_unique_id () : int =
   if !unique_id >= Pervasives.max_int then (
      (* if we have run out of unique integers, die *)
      parse_error "ran out of unique IDs"
   ) else (
     unique_id := (!unique_id + 1);
     !unique_id
   )
;;

let add_symbol (s : string) : int = 
   try Hashtbl.find symbol_table s
   with _ -> (
      let id = get_unique_id () in
      let len = String.length s in
      if (len > !max_symbol_len) then max_symbol_len := len;
      Hashtbl.replace symbol_table s id;
      id
   )
;;

let get_unique_symbol (prefix : string) : int =
   let id = get_unique_id () in
   let ids = string_of_int id in
   let num = (max 0 (!max_symbol_len -
                    (String.length prefix) - (String.length ids))) in
   Hashtbl.replace symbol_table (prefix^(String.make num '0')^ids) id;
   id
;;

let get_id (sym : string) : int =
   try Hashtbl.find symbol_table sym
   with _ -> 0
;; 

let get_symbol (id : int) : string =
   let res = Hashtbl.fold (fun k v i ->
      match i with
      | None -> if (v = id) then Some(k) else None
      | _ -> i
   ) symbol_table None in
   match res with
   | None -> parse_error ("could not find symbol: "^(string_of_int id))
   | Some(s) -> s
;;

let rec explode (s : string) : (char list) =
  let len = String.length s in
  if len = 0 then []
  else if len = 1 then [String.get s 0]
  else (
     let c = String.get s 0 in
     let rest = String.sub s 1 (len-1) in
     c::(explode rest)
  )
;;

let rec implode (cl : char list) : string =
   match cl with
   | [] -> ""
   | c::more -> ((String.make 1 c)^(implode more))
;;

let encode_int (i : int) : int64 =
   Int64.add (Int64.mul (Int64.of_int i) 2L) 1L
;;

module StringSet = Set.Make(String);;

let debug_table = ref (StringSet.empty : StringSet.t);;

let add_debug (d : string) : unit =
   debug_table := StringSet.add d !debug_table
;;

let has_debug (d : string) : bool =
   StringSet.mem d !debug_table
;;

let heap_size = ref 1048576;;

let set_heap_size (hs : int) : unit =
   heap_size := hs
;;

let get_heap_size () : int =
   !heap_size
;;
