let print_list l = List.iter (fun i -> print_int i; print_string ", ") l; print_string "\n";;

let answer = [1;-2;-3;4];;
let clauses = [[1;2;3;4;5;6];[-1;2;-4];[1;5;6]];;
let abs x = if 0 < x then x else 0 - x;;
let rec clause_contains cs x =
   if (List.length cs <= 0) then false else (if ((abs (List.hd cs)) == (abs x)) then true else (clause_contains (List.tl cs) x));;
let rec concat_all l = if (List.length l <= 0) then [] else ((List.hd l)@(concat_all (List.tl l)));;
let rec get_all_vars_helper l = if (List.length l <= 0) then [] else
   (let x = (abs (List.hd l)) in let y = (get_all_vars_helper (List.tl l)) in if (clause_contains y x) then y else x::y);;
let get_all_vars cs = let l = concat_all cs in List.sort compare (get_all_vars_helper l);;

let temp = (get_all_vars clauses) in
print_list temp;;
