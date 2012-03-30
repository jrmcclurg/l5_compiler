type pos = NoPos | Pos of string*int*int;; (* file,line,col *)

type grammar = Grammar of pos * code * code * production list (* code,prods *)
 and code = Code of pos * string option
 and production = Production of pos * string * pattern list (* name,patterns *)
 and pattern = Pattern of pos * subpattern list * string * code (* subpatterns,code *)
 and subpattern = SimpleSubpattern of pos * atom * opts
                | RangeSubpattern of pos * atom * atom * opts
 and atom = EOFAtom of pos
          | IdentAtom of pos * string
          | StringAtom of pos * string
          | CharsetsAtom of pos * charsets
          | ChoiceAtom of pos * subpatterns list
 and subpatterns = Subpatterns of pos * subpattern list
 and charsets = SingletonCharsets of pos * charset
              | DiffCharsets of pos * charset * charset
 and charset = WildcardCharset of pos
             | SingletonCharset of pos * char 
             | ListCharset of pos * chars list * bool
 and chars = SingletonChars of pos * char
           | RangeChars of pos * char * char
 and opts = Options of pos * op option * int option * assoc option
 and op = StarOp of pos
        | PlusOp of pos
        | QuestionOp of pos
 and assoc = LeftAssoc of pos
           | RightAssoc of pos
           | UnaryAssoc of pos
;;

let rec string_explode (s:string) : char list =
   if (String.length s) > 0 then
      (String.get s 0)::(string_explode (String.sub s 1 ((String.length s)-1)))
   else
      []
;;

let three_hd (cl: char list) : char list * char list = 
   match cl with
   | a::b::c::l -> (a::b::c::[],l)
   | a::b::l    -> (a::b::[],l)
   | a::l       -> (a::[],l)
   | _          -> ([],cl)
;;

let rec compile_char_list (cl: char list) : chars list = 
   let (hd,tl) = three_hd cl in
   match hd with
   | a::'-'::c::[] -> (RangeChars(NoPos,a,c))::(compile_char_list tl)
   | a::b::c::[]   -> (SingletonChars(NoPos,a))::(compile_char_list (b::c::tl))
   | a::b::[]      -> (SingletonChars(NoPos,a))::(compile_char_list (b::tl))
   | a::[]         -> (SingletonChars(NoPos,a))::(compile_char_list (tl))
   | _             -> []
;;

let compile_charset (s:string) : chars list * bool =
   let l = string_explode s in
   match l with
   | '^'::cs -> (compile_char_list cs, true)
   | _       -> (compile_char_list l , false)
;;

let char_of_string (s:string) : char =
   let s2 = Str.global_replace (Str.regexp_string "\\[") "[" s in
   let s3 = Str.global_replace (Str.regexp_string "\\]") "]" s2 in
   Scanf.sscanf s3 "%C" (fun x -> x)
;;

let string_of_string (s:string) : string =
   let s2 = Str.global_replace (Str.regexp_string "\\[") "[" s in
   let s3 = Str.global_replace (Str.regexp_string "\\]") "]" s2 in
   Scanf.sscanf s3 "%S" (fun x -> x)
;;

let rec print_indent2 n s =
   if n=0 then print_string s
   else (print_string " "; print_indent2 (n-1) s)
and print_indent n s =
   print_indent2 (n*3) s
;;

let rec print_grammar (n:int) (g:grammar) : unit =
   match g with
   | Grammar(p,c1,c2,pl) ->
      print_indent n "Grammar(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_code (n+1) c1;
      print_string ",\n";
      print_code (n+1) c2;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag pr -> 
         if flag then print_string ",\n";
         print_production (n+2) pr;
         true
      ) false pl in (); 
      print_string "\n";
      print_indent (n+1) "]\n";
      print_indent n ")";

and print_code (n:int) (c:code) : unit =
   match c with
   | Code(p,st) ->
      print_indent n "Code(\n";
      print_pos (n+1) p;
      print_string ",\n";
      (match st with
      | None -> print_indent (n+1) "None"
      | Some(s) -> print_str (n+1) s);
      print_string "\n";
      print_indent n ")";

and print_str (n:int) (s:string) : unit =
   print_indent n ("\""^(String.escaped s)^"\"")

and print_chr (n:int) (c:char) : unit =
   print_indent n ("'"^(Char.escaped c)^"'")

and print_bl (n:int) (b:bool) : unit =
   print_indent n (if b then "true" else "false")

and print_regex (n:int) (s:string) : unit =
   print_indent n ("["^(String.escaped s)^"]") (* TODO - maybe escape this? *)

and print_prec (n:int) (i:int option) : unit =
   match i with
   | None -> print_indent n "None"
   | Some(k) ->
      print_indent n "";
      print_int k

and print_pos (n:int) (p:pos) : unit =
   match p with
   | NoPos -> print_indent n "NoPos"
   | Pos(f,l,m) ->
      print_indent n "Pos(\"";
      print_string f;
      print_string "\",";
      print_int l;
      print_string ",";
      print_int m;
      print_string ")";

and print_production (n:int) (pr:production) : unit =
   match pr with
   | Production(p,name,pl) ->
      print_indent n "Production(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_str (n+1) name;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag pa ->
         if flag then print_string ",\n";
         print_pattern (n+2) pa;
         true;
      ) false pl in ();
      print_string "\n";
      print_indent (n+1) "]\n";
      print_indent n ")";

and print_pattern (n:int) (pa:pattern) : unit =
   match pa with
   | Pattern(p,sl,label,s) ->
      print_indent n "Pattern(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag sp ->
         if flag then print_string ",\n";
         print_subpattern (n+2) sp;
         true;
      ) false sl in ();
      print_string "\n";
      print_indent (n+1) "],\n";
      print_indent (n+1) label;
      print_string "\n";
      print_code (n+1) s;
      print_string "\n";
      print_indent n ")";

and print_subpattern (n:int) (sp:subpattern) : unit =
   match sp with
   | SimpleSubpattern(p,a,o) ->
      print_indent n "SimpleSubpattern(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_atom (n+2) a;
      print_string ",\n";
      print_opts (n+1) o;
      print_string "\n";
      print_indent n ")";
   | RangeSubpattern(p,a1,a2,o) ->
      print_indent n "RangeSubpattern(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_atom (n+2) a1;
      print_string ",\n";
      print_atom (n+2) a2;
      print_string ",\n";
      print_opts (n+1) o;
      print_string "\n";
      print_indent n ")";

and print_atom (n:int) (a:atom) : unit =
   match a with
   | EOFAtom(p) ->
      print_indent n "EOFAtom(";
      print_pos 0 p;
      print_indent n ")";
   | IdentAtom(p,s) ->
      print_indent n "IdentAtom(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_str (n+1) s;
      print_string "\n";
      print_indent n ")";
   | StringAtom(p,s) ->
      print_indent n "StringAtom(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_str (n+1) s;
      print_string "\n";
      print_indent n ")";
   | CharsetsAtom(p,c) ->
      print_indent n "CharsetsAtom(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_charsets (n+1) c;
      print_string "\n";
      print_indent n ")"
   | ChoiceAtom(p,sl) ->
      print_indent n "ChoiceAtom(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag sp ->
         if flag then print_string ",\n";
         print_subpatterns (n+2) sp;
         true;
      ) false sl in ();
      print_string "\n";
      print_indent (n+1) "],\n";
      print_indent n ")"

and print_subpatterns (n:int) (s:subpatterns) : unit =
   match s with
   | Subpatterns(p,sl) ->
      print_indent n "Subpatterns(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag sp ->
         if flag then print_string ",\n";
         print_subpattern (n+2) sp;
         true;
      ) false sl in ();
      print_string "\n";
      print_indent (n+1) "],\n";
      print_indent n ")"

and print_charsets (n:int) (cs:charsets) : unit =
   match cs with
   | SingletonCharsets(p,c) ->
      print_indent n "SingletonCharsets(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_charset (n+1) c;
      print_string "\n";
      print_indent n ")";
   | DiffCharsets(p,c1,c2) ->
      print_indent n "DiffCharsets(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_charset (n+1) c1;
      print_string ",\n";
      print_charset (n+1) c2;
      print_string "\n";
      print_indent n ")"

and print_charset (n:int) (c:charset) : unit =
   match c with
   | WildcardCharset(p) ->
      print_indent n "WildcardCharset(";
      print_pos 0 p;
      print_indent n ")";
   | SingletonCharset(p,c) ->
      print_indent n "SingletonCharset(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_chr (n+1) c;
      print_string "\n";
      print_indent n ")"
   | ListCharset(p,cl,b) ->
      print_indent n "ListCharset(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_indent (n+1) "[\n";
      let _ = List.fold_left (fun flag a ->
         if flag then print_string ",\n";
         print_chars (n+2) a;
         true;
      ) false cl in ();
      print_string "\n";
      print_indent (n+1) "],\n";
      print_bl (n+1) b;
      print_string "\n";
      print_indent n ")"

and print_chars (n:int) (crs:chars) : unit =
   match crs with
   | SingletonChars(p,c) ->
      print_indent n "SingletonChars(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_chr (n+1) c;
      print_string "\n";
      print_indent n ")";
   | RangeChars(p,c1,c2) ->
      print_indent n "RangeChars(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_chr (n+1) c1;
      print_string ",\n";
      print_chr (n+1) c2;
      print_string "\n";
      print_indent n ")"

and print_opts (n:int) (o1:opts) : unit =
   match o1 with
   | Options(p,o,i,a) ->
      print_indent n "Options(\n";
      print_pos (n+1) p;
      print_string ",\n";
      print_op (n+1) o;
      print_string ",\n";
      print_prec (n+1) i;
      print_string ",\n";
      print_assoc (n+1) a;
      print_string "\n";
      print_indent n ")";

and print_op (n:int) (o:op option) : unit =
   match o with
   | None -> print_indent n "None";
   | Some(StarOp(p)) ->
      print_indent n "StarOp(";
      print_pos 0 p;
      print_string ")";
   | Some(PlusOp(p)) ->
      print_indent n "PlusOp(";
      print_pos 0 p;
      print_string ")";
   | Some(QuestionOp(p)) ->
      print_indent n "QuestionOp(";
      print_pos 0 p;
      print_string ")";

and print_assoc (n:int) (a:assoc option) : unit =
   match a with
   | None -> print_indent n "None"
   | Some(LeftAssoc(p)) ->
      print_indent n "LeftAssoc(";
      print_pos 0 p;
      print_string ")";
   | Some(RightAssoc(p)) ->
      print_indent n "RightAssoc(";
      print_pos 0 p;
      print_string ")";
   | Some(UnaryAssoc(p)) ->
      print_indent n "UnaryAssoc(";
      print_pos 0 p;
      print_string ")";
;;
