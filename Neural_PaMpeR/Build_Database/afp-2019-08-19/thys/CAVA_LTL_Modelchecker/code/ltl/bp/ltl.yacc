open Ltl_Dt
open Propc
%%
%name Ltl

%term NOT    | OR     | AND 
    | IMPL   | IFF
    | TRUE   | FALSE
    | NEXT   | FINAL  | GLOBAL
    | UNTIL  | RELEASE
    | LPAREN | RPAREN
    | IDENT of string
    | IDENT_ARG of int
    | EOF | BAD_CHAR

%left IFF
%left IMPL
%left AND OR
%left UNTIL RELEASE

%nonassoc NEXT FINAL GLOBAL
%nonassoc NOT

%nonterm input of propc ltlc 
       | formula of propc ltlc
       | ident of propc

%pos int

%eop EOF
%noshift EOF

(* %verbose *)
%start input
%pure

%%

input: formula (formula)

formula: ident			 (Prop_ltlc ident)
       | TRUE			 (True_ltlc)
       | FALSE			 (False_ltlc)
       | NOT formula		 (Not_ltlc formula)
       | NEXT formula		 (Next_ltlc formula)
       | FINAL formula		 (Final_ltlc formula)
       | GLOBAL formula		 (Global_ltlc formula)
       | formula OR formula	 (Or_ltlc (formula1, formula2))
       | formula AND formula 	 (And_ltlc (formula1, formula2))
       | formula IMPL formula (Implies_ltlc (formula1, formula2))
       | formula UNTIL formula	 (Until_ltlc (formula1, formula2))
       | formula RELEASE formula (Release_ltlc (formula1, formula2))
       | LPAREN formula RPAREN   (formula)

ident: IDENT IDENT_ARG  (FProp (IDENT, IDENT_ARG))
     | IDENT            (CProp IDENT)

(* 
 * vim: ft=yacc 
 *)
