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
    | LBRACK | RBRACK
    | EQ | NEQ | GR | GEQ | LE | LEQ
    | IDENT of string
    | IDENT_EXPR of int
    | EOF | BAD_CHAR

%left IFF
%left IMPL
%left AND OR
%left UNTIL RELEASE

%nonassoc NEXT FINAL GLOBAL
%nonassoc NOT

%nonterm input of propc ltlc 
       | formula of propc ltlc
       | expr of propc ltlc
       | ident of ident
       | bop of binOp

%pos int

%eop EOF
%noshift EOF

(* %verbose *)
%start input
%pure

%%

input: formula (formula)

formula: expr			 (expr)
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

ident: IDENT LBRACK IDENT_EXPR RBRACK      (Ident (IDENT, SOME IDENT_EXPR))
     | IDENT                (Ident (IDENT, NONE))

expr: ident NEQ IDENT_EXPR (Not_ltlc (Prop_ltlc (BExpProp (Eq, ident, IDENT_EXPR))))
    | ident NEQ ident      (Not_ltlc (Prop_ltlc (BProp (Eq, ident1, ident2))))
    | ident bop IDENT_EXPR  (Prop_ltlc (BExpProp (bop, ident, IDENT_EXPR)))
    | ident bop ident       (Prop_ltlc (BProp (bop, ident1, ident2)))
    | ident                 (Prop_ltlc (CProp ident))

bop: EQ  (Eq)
  | LE  (Le)
  | LEQ (LEq)
  | GR  (Gr)
  | GEQ (GEq)

(* 
 * vim: ft=yacc 
 *)
