chapter "Examples"

section "Example Datatypes"

theory Derive_Datatypes
imports Main
begin

(* Simple type without recursion or parameters *)
datatype simple = A (num: nat) | B (left:nat) (right:nat) | C 
  
(* type with parameters *)  
datatype ('a,'b) either = L 'a | R 'b
  
(* recursive type *)
datatype 'a tree = Leaf | Node 'a "'a tree" "'a tree"     
  
(* mutually recursive types *)
  
datatype even_nat = Even_Zero | Even_Succ odd_nat
   and   odd_nat  = Odd_Succ even_nat  
   
datatype ('a,'b) exp = Term "('a,'b) trm" | Sum (left:"('a,'b) trm") (right:"('a,'b) exp")
and      ('a,'b) trm = Factor "('a,'b) fct " | Prod "('a,'b) fct " "('a,'b) trm "
and      ('a,'b) fct = Const 'a | Var (v:'b) | Expr "('a,'b) exp"

end