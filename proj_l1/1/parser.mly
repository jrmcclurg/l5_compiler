/* File parser.mly */
%{
   open Ast;;
   open Utils;;
%}
%token <int> INT
%token <string> IDENT
%token <Lexing.position*string option> CODE
%token <string> STRINGQUOT 
%token <string> CHARSET
%token <char> CHARQUOT
%token PLUS MINUS TIMES DIV
%token LPAREN RPAREN
%token EOL
%token RANGE
%token EOF
%token COLON SEMI LBRACK RBRACK
%token LEFT RIGHT UNARY
%token ARROW BAR DQUOT QUOT STAR PLUS QUESTION WILDCARD DIFF ENDFILE
%left PLUS MINUS /* lowest precedence */
%left TIMES DIV /* medium precedence */
%nonassoc UMINUS /* highest precedence */
%start main /* the entry point */
%type <Ast.grammar> main
%%
main:
   code_block production prod_list code_block EOF {
      match $1 with
      | Code(p,_) ->
         Grammar((if p=NoPos then get_pos (rhs_start_pos 2) else
            p),$1,$4,$2::$3)
   }
;

code_block:
          { Code(NoPos,None) }
   | CODE { let (p,s) = $1 in Code(get_pos p,s) }

prod_list:
                          { [] }
   | production prod_list { $1::$2 }
;

production:
   IDENT ARROW pattern pattern_bar_list SEMI { Production(get_current_pos (),$1,$3::$4) }
;

pattern_bar_list:
                              { [] }
   | BAR pattern pattern_bar_list { $2::$3 } 
;

pattern:
   subpattern subpattern_list label code_block { Pattern(get_current_pos (),$1::$2,$3,$4) }
;

label:
                 { "" }
   | COLON IDENT { $2 }
;

subpattern_list:
                                { [] }
   | subpattern subpattern_list { $1::$2 }
;

subpattern:
     atom opts                    { SimpleSubpattern(get_current_pos (),$1,$2) }
   | atom RANGE atom opts         { RangeSubpattern(get_current_pos (),$1,$3,$4) }
;

atom:
     ENDFILE    { EOFAtom(get_current_pos ()) }
   | IDENT      { IdentAtom(get_current_pos (),$1) }
   | STRINGQUOT { StringAtom(get_current_pos (),$1) }
   | charsets   { CharsetsAtom(get_current_pos(),$1) }
  /*  | atom RANGE atom { RangeAtom(get_current_pos(),$1,$3) } */
    | LPAREN subpatterns subpatterns_bar_list RPAREN {
      ChoiceAtom(get_current_pos (),$2::$3) } 
;

subpatterns_bar_list:
                                     { [] }
   | BAR subpatterns subpatterns_bar_list { $2::$3 }
;

subpatterns:
     subpattern subpattern_list { Subpatterns(get_current_pos (),$1::$2) }

charsets:
     charset              { SingletonCharsets(get_current_pos (),$1) } 
   | charset DIFF charset { DiffCharsets(get_current_pos (),$1,$3) } 

charset:
     WILDCARD { WildcardCharset(get_current_pos ()) }
   | CHARQUOT { SingletonCharset(get_current_pos (),$1) }
   | CHARSET  { let (l,b) = Ast.compile_charset $1 in
                ListCharset(get_current_pos (),l,b) }

opts:
   op_opr op_int op_assoc {
      Options(get_current_pos (),$1,$2,$3)
   }
;

op_opr:
          { None }
   | STAR { Some(StarOp(get_current_pos ())) }
   | PLUS { Some(PlusOp(get_current_pos ())) }
   | QUESTION { Some(QuestionOp(get_current_pos ())) }
;

op_int:
         { None }
   | INT { Some($1) }
;

op_assoc:
           { None }
   | LEFT  { Some(LeftAssoc(get_current_pos ())) }
   | RIGHT { Some(RightAssoc(get_current_pos ())) }
   | UNARY { Some(UnaryAssoc(get_current_pos ())) }
;
