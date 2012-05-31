let print_list l = List.iter (fun i -> print_int i; print_string ", ") l; print_string "\n";;

let answer = [1;-2;-3;4];;
let clauses = [[1;2;3;4;5;6];[-1;2;-4];[-1;2;3;6]];;
let abs x = if 0 < x then x else 0 - x;;
let rec clause_contains cs x =
   if (List.length cs <= 0) then false else (if ((abs (List.hd cs)) == (abs x)) then true else (clause_contains (List.tl cs) x));;
let rec concat_all l = if (List.length l <= 0) then [] else ((List.hd l)@(concat_all (List.tl l)));;
let rec get_all_vars_helper l = if (List.length l <= 0) then [] else
   (let x = (abs (List.hd l)) in let y = (get_all_vars_helper (List.tl l)) in if (clause_contains y x) then y else x::y);;
let get_all_vars cs = let l = concat_all cs in List.sort compare (get_all_vars_helper l);;
let rec clause_union (a : int list) (b : int list) =
   if (List.length a) <= 0 then b
   else (let rest = (clause_union (List.tl a) b) in (if (clause_contains b (List.hd a)) then rest else ((List.hd a)::rest)));;
let rec propagate_literal (clause : int list) (lit : int) : (int list) =
   if (List.length clause) <= 0 then [] else
   (let head = (List.hd clause) in
   (let rest = (propagate_literal (List.tl clause) lit) in (if lit == (0 - head) then rest else (head::rest ))));;
let rec propagate_to_clause (clause : int list) (temp_answer : int list) : (int list) = 
   if ((List.length temp_answer) <= 0) then clause else (
   if ((List.length clause) <= 0) then [] else
   (let x = (propagate_literal clause (List.hd temp_answer)) in (propagate_to_clause x (List.tl temp_answer))));;
let rec propagate (clauses : (int list) list) (temp_answer : int list) : (int list) =
   if (List.length clauses) <= 0 then []
   else (
      let x = (propagate_to_clause (List.hd clauses) temp_answer) in
      (clause_union (if (List.length x) == 1 then x else []) (propagate (List.tl clauses) temp_answer))
   );;

let temp = (get_all_vars clauses) in
print_list temp;;

let temp2 = (propagate clauses answer) in
print_list temp2;;
