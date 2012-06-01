let print_list l = List.iter (fun i -> print_int i; print_string " ") l; print_string "\n";;

let clauses = [
[4;-18;19];
[3;18;-5];
[-5;-8;-15];
[-20;7;-16];
[10;-13;-7];
[-12;-9;17];
[17;19;5];
[-16;9;15];
[11;-5;-14];
[18;-10;13];
[-3;11;12];
[-6;-17;-8];
[-18;14;1];
[-19;-15;10];
[12;18;-19];
[-8;4;7];
[-8;-9;4];
[7;17;-15];
[12;-7;-14];
[-10;-11;8];
[2;-15;-11];
[9;6;1];
[-11;20;-17];
[9;-15;13];
[12;-7;-17];
[-18;-2;20];
[20;12;4];
[19;11;14];
[-16;18;-4];
[-1;-17;-19];
[-13;15;10];
[-12;-14;-13];
[12;-14;-7];
[-7;16;10];
[6;10;7];
[20;14;-16];
[-19;17;11];
[-7;1;-20];
[-5;12;15];
[-4;-9;-13];
[12;-11;-7];
[-5;19;-8];
[1;16;17];
[20;-14;-15];
[13;-4;10];
[14;7;10];
[-5;9;20];
[10;1;-19];
[-16;-15;-1];
[16;3;-11];
[-15;-10;4];
[4;-15;-3];
[-10;-16;11];
[-8;12;-5];
[14;-6;12];
[1;6;11];
[-13;-5;-1];
[-7;-2;12];
[1;-20;19];
[-2;-13;-8];
[15;18;4];
[-11;14;9];
[-6;-15;-2];
[5;-12;-15];
[-6;17;5];
[-13;5;-19];
[20;-1;14];
[9;-17;15];
[-5;19;-18];
[-12;8;-10];
[-18;14;-4];
[15;-9;13];
[9;-5;-1];
[10;-19;-14];
[20;9;4];
[-9;-2;19];
[-5;13;-17];
[2;-10;-18];
[-18;3;11];
[7;-9;17];
[-15;-6;-3];
[-2;3;-13];
[12;3;-2];
[-2;-3;17];
[20;-15;-16];
[-5;-17;-19];
[-20;-18;11];
[-9;1;-5];
[-19;9;17];
[12;-2;17];
[4;-16;-5]
];;

let answer = [1;-2;-3;-14];;
(*let clauses = [[-1;-2;3;4;5;6];[1;2;-3;14];[1;-2;3;6]];;*)
let abs x = if 0 < x then x else 0 - x;;
let rec clause_contains cs x =
   if (List.length cs <= 0) then false else (if ((abs (List.hd cs)) == (abs x)) then true else (clause_contains (List.tl cs) x));;
let rec concat_all (l : (int list) list) = if (List.length l <= 0) then [] else ((List.hd l)@(concat_all (List.tl l)));;
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
   if (List.length clauses) <= 0 then ([],1)
   else (
      let (x,res) = (propagate_to_clause (List.hd clauses) temp_answer) in
      let (x2,res2) = (propagate (List.tl clauses) temp_answer) in
      ((clause_diff (clause_union (if (List.length x) == 1 then x else []) x2) temp_answer),
        if (res==1 && res2==1) then 1 else (if (res==(-1) || res2==(-1)) then (-1) else 0))
   );;
let rec add_guess (temp_answer : int list) (flags : int list) (literals : int list) : (int list * int list * bool) =
   if (List.length literals) <= 0 then (temp_answer,flags,false)
   else let (rest,rest_flags,b) = (add_guess temp_answer flags (List.tl literals)) in
   (if (clause_contains temp_answer (List.hd literals)) || b then (rest,rest_flags,b) else
   (rest@[(List.hd literals)],rest_flags@[1],true));;
let rec add_propagated (temp_answer : int list) (flags : int list) (to_add : int list) : (int list * int list) =
   if (List.length to_add) <= 0 then (temp_answer,flags) else
   let (ans2,flags2) = add_propagated temp_answer flags (List.tl to_add) in (ans2@[List.hd to_add],flags2@[0]);;
let rec undo_guess (temp_answer : int list) (flags : int list) : (int list * int list * bool) =
   if (List.length temp_answer) <= 0 then (temp_answer,flags,false) else (
   let (ans2,flags2,t) = undo_guess (List.tl temp_answer) (List.tl flags) in
   if t then ((List.hd temp_answer)::ans2,(List.hd flags)::flags2,t) else
   (if (List.hd flags)==1 then (ans2@[0 - (List.hd temp_answer)],flags2@[(List.hd flags)+1],true) else (ans2,flags2,t)));;
let rec sat_helper (clauses: (int list) list) (temp_answer : int list) (temp_answer_flags : int list) (literals : int list) (n : int) : (bool * int list * int) =
   let (temp_answer2,temp_answer_flags2,_) = add_guess temp_answer temp_answer_flags literals in
   (*print_string "Trying: ";
   print_list temp_answer2;*)
   let (res,x) = propagate clauses temp_answer2 in
   if x==1 then (true,clause_union temp_answer2 res,n) else
   (if x==(-1) || (List.length temp_answer2)==(List.length literals) then (
      let (temp_answer3,temp_answer_flags3,_) = undo_guess temp_answer2 temp_answer_flags2 in
      if (List.length temp_answer3 <= 0) then (false,[],n)
      else sat_helper clauses temp_answer3 temp_answer_flags3 literals (n+1)
   ) else (
      let (new_answer,new_answer_flags) = add_propagated temp_answer2 temp_answer_flags2 res in
      sat_helper clauses new_answer new_answer_flags literals (n+1)
   ));;
let sat (clauses : (int list) list) : (bool * int list) =
   let literals = (get_all_vars clauses) in
   let (is_sat,assignment,n) = sat_helper clauses [] [] literals 1 in
   print_string ("Iterations: "^(string_of_int n)^"\n");
   (is_sat,List.sort compare assignment)
;;

let (is_sat,assignment) = sat clauses in
print_string ("SAT? "^(if is_sat then "YES" else "NO")^"\n");
print_list assignment;;

print_string "---\n";;

let temp = (get_all_vars clauses) in
print_list temp;

let (temp2,result) = (propagate clauses [1]) in
print_list temp2;
print_int result;
print_string "\n";;
