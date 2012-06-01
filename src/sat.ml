let print_list l = List.iter (fun i -> print_int i; print_string ", ") l; print_string "\n";;

let answer = [1;-2;-3;-14];;
let clauses = [[1;2;3;4;5;6];[-1;2;3;14];[-1;2;3;6]];;
let abs x = if 0 < x then x else 0 - x;;
let rec clause_contains cs x =
   if (List.length cs <= 0) then false else (if ((abs (List.hd cs)) == (abs x)) then true else (clause_contains (List.tl cs) x));;
let rec concat_all l = if (List.length l <= 0) then [] else ((List.hd l)@(concat_all (List.tl l)));;
let rec get_all_vars_helper l = if (List.length l <= 0) then [] else
   (let x = (abs (List.hd l)) in let y = (get_all_vars_helper (List.tl l)) in if (clause_contains y x) then y else x::y);;
let get_all_vars cs = let l = concat_all cs in List.rev (List.sort compare (get_all_vars_helper l));;
let rec clause_union_helper (ab : int list) : int list =
   if (List.length ab) <= 0 then []
   else
   (let rest = (clause_union_helper (List.tl ab)) in
   (if (clause_contains rest (List.hd ab)) then rest else ((List.hd ab)::rest)));;
let clause_union (a : int list) (b : int list) : int list =
   clause_union_helper (a@b);;
let rec clause_diff (a : int list) (b : int list) : int list =
   if (List.length a) <= 0 then []
   else
   (let rest = (clause_diff (List.tl a) b) in
   (if (clause_contains b (List.hd a)) || (clause_contains rest (List.hd a)) then rest else ((List.hd a)::rest)));;
let rec propagate_literal (clause : int list) (lit : int) : (int list * int) =
   if (List.length clause) <= 0 then ([],-1) else
   (let head = (List.hd clause) in
   (let (rest,res) = (propagate_literal (List.tl clause) lit) in (if lit == (0 - head) then
   (rest,if res >= 0 then res else (-1)) else (head::rest,if (lit==head || res==1) then 1 else 0))));;
let rec propagate_to_clause (clause : int list) (temp_answer : int list) : (int list * int) = 
   if ((List.length clause) <= 0) then ([],-1) else
   if ((List.length temp_answer) <= 0) then (clause,0) else (
   (let (x,res) = (propagate_literal clause (List.hd temp_answer)) in
   let (y,res2) = (propagate_to_clause x (List.tl temp_answer)) in
   (y,if (res==1 || res2==1) then 1 else (if (res2==(-1)) then (-1) else 0))));;
let rec propagate (clauses : (int list) list) (temp_answer : int list) : (int list * int) =
   if (List.length clauses) <= 0 then ([],0)
   else (
      let (x,res) = (propagate_to_clause (List.hd clauses) temp_answer) in
      let (x2,res2) = (propagate (List.tl clauses) temp_answer) in
      ((clause_diff (clause_union (if (List.length x) == 1 then x else []) x2) temp_answer),
        if (res==1 && res2==1) then 1 else (if (res==(-1) || res2==(-1)) then (-1) else 0))
   );;
let rec add_guess (temp_answer : int list) (flags : int list) (literals : int list) : (int list * int list * bool) =
   if (List.length literals) <= 0 then (temp_answer,flags,false)
   else let (rest,rest_flags,b) = (add_guess temp_answer flags (List.tl literals)) in
   (if (clause_contains temp_answer (List.hd literals)) || b then (rest,rest_flags,b) else (rest@[(List.hd literals)],rest_flags@[1],true));;
let rec add_propagated (temp_answer : int list) (flags : int list) (to_add : int list) : (int list * int list) =
   if (List.length to_add) <= 0 then (temp_answer,flags) else
   let (ans2,flags2) = add_propagated temp_answer flags (List.tl to_add) in (ans2@[List.hd to_add],flags2@[0]);;
let rec undo_guess (temp_answer : int list) (flags : int list) : (int list * int list * bool) =
   if (List.length temp_answer) <= 0 then (temp_answer,flags,false) else (
   let (ans2,flags2,t) = undo_guess (List.tl temp_answer) (List.tl flags) in
   if t then ((List.hd temp_answer)::ans2,(List.hd flags)::flags2,t) else
   (if (List.hd flags)==1 then (ans2@[0 - (List.hd temp_answer)],flags2@[(List.hd flags)+1],true) else (ans2,flags2,t)));;
(*let rec sat_helper (clauses: (int list) list) (temp_answer : int list) (temp_answer_flags : int list) (literals : int list) : (bool * int list) =
   let (temp_answer2,temp_answer_flags2) = add_guess temp_answer temp_answer_flags literals in
   let (x,res) = propagate clauses temp_answer2 in
   if x==1 then (true,clause_union temp_answer2 res) else
   (if x==(-1) then (
      let (temp_answer3,temp_answer_flags3) = undo_guess temp_answer2 temp_answer_flags2 in
      if (List.length temp_answer3 <= 0) then (false,[])
      else sat_helper clauses temp_answer3 temp_answer_flags3 literals
   ) else (
      let new_answer = add_propagated temp_answer2 temp_answer_flags2 res in
      sat_helper clauses new_answer literals
   ));;*)

let temp = (get_all_vars clauses) in
print_list temp;

let (temp_ans,temp_flags) = ([1;2;3;2;3;4;5],[0;1;0;0;1;0;1]) in
let (ans,flags) = add_propagated temp_ans temp_flags temp in
print_list ans;
print_list flags;
let (blah,blah2,_) = undo_guess ans flags in
print_list blah;
print_list blah2;
let (blah,blah2,_) = undo_guess blah blah2 in
print_list blah;
print_list blah2;
let (blah,blah2,_) = undo_guess blah blah2 in
print_list blah;
print_list blah2;
let (blah,blah2,_) = undo_guess blah blah2 in
print_list blah;
print_list blah2
;;

print_string "---\n";;

let (temp2,result) = (propagate clauses answer) in
print_list temp2;
print_int result;
print_string "\n";;
