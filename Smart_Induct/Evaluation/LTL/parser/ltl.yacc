open Ltl_Dt
%%
%name Ltl

%term NOT       | OR            | AND
    | IMPL      | IFF
    | TRUE      | FALSE
    | NEXT      | FINAL         | GLOBAL
    | UNTIL     | RELEASE
    | WEAKUNTIL | STRONGRELEASE
    | LPAREN    | RPAREN
    | IDENT of string
    | EOF       | BAD_CHAR

%left IFF
%left IMPL
%left AND OR
%left UNTIL RELEASE
%left WEAKUNTIL STRONGRELEASE

%nonassoc NEXT FINAL GLOBAL
%nonassoc NOT

%nonterm input of string ltlc 
       | formula of string ltlc

%pos int

%eop EOF
%noshift EOF

(* %verbose *)
%start input
%pure

%%

input: formula (formula)

formula: IDENT                         (Prop_ltlc IDENT)
       | TRUE                          (True_ltlc)
       | FALSE                         (False_ltlc)
       | NOT formula                   (Not_ltlc formula)
       | NEXT formula                  (Next_ltlc formula)
       | FINAL formula                 (Final_ltlc formula)
       | GLOBAL formula                (Global_ltlc formula)
       | formula OR formula            (Or_ltlc (formula1, formula2))
       | formula AND formula           (And_ltlc (formula1, formula2))
       | formula IMPL formula          (Implies_ltlc (formula1, formula2))
       | formula IFF formula           (iff_ltlc formula1 formula2)
       | formula UNTIL formula         (Until_ltlc (formula1, formula2))
       | formula RELEASE formula       (Release_ltlc (formula1, formula2))
       | formula WEAKUNTIL formula     (WeakUntil_ltlc (formula1, formula2))
       | formula STRONGRELEASE formula (StrongRelease_ltlc (formula1, formula2))
       | LPAREN formula RPAREN         (formula)

(* 
 * vim: ft=yacc 
 *)
