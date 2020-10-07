section "Show"

theory Derive_Show
imports Main "../Derive" Derive_Datatypes
begin

class showable =
  fixes print :: "'a \<Rightarrow> string"

fun string_of_nat :: "nat \<Rightarrow> string"
where
  "string_of_nat n = (if n < 10 then [(char_of :: nat \<Rightarrow> char) (48 + n)] else
     string_of_nat (n div 10) @ [(char_of :: nat \<Rightarrow> char) (48 + (n mod 10))])"

(* Manual instances for nat, unit, prod, and sum *)
instantiation nat and unit:: showable
begin
  definition print_nat: "print (n::nat) = string_of_nat n"
  definition print_unit: "print (x::unit) = ''''"
  instance ..
end

instantiation Tagged_Prod_Sum.prod and Tagged_Prod_Sum.sum :: (showable, showable) showable
begin
definition print_prod_def: 
  "print (x::('a,'b) Tagged_Prod_Sum.prod) = 
    (case Tagged_Prod_Sum.sel_name_fst x of 
        None \<Rightarrow> (print (Tagged_Prod_Sum.fst x)) 
      | Some s \<Rightarrow> ''('' @ s @ '': '' @ (print (Tagged_Prod_Sum.fst x)) @ '')'')
    @
    '' '' 
    @
    (case Tagged_Prod_Sum.sel_name_snd x of 
        None \<Rightarrow> (print (Tagged_Prod_Sum.snd x)) 
      | Some s \<Rightarrow> ''('' @ s @ '': '' @ (print (Tagged_Prod_Sum.snd x)) @ '')'')"

definition print_sum_def:  "print (x::('a,'b) Tagged_Prod_Sum.sum) = 
  (case x of (Tagged_Prod_Sum.Inl s a) \<Rightarrow> (case s of None \<Rightarrow> print a | Some c \<Rightarrow> ''('' @ c @ '' '' @ (print a) @ '')'')
           | (Tagged_Prod_Sum.Inr s b) \<Rightarrow> (case s of None \<Rightarrow> print b | Some c \<Rightarrow> ''('' @ c @ '' '' @ (print b) @ '')''))"
  instance ..
end

(* simple types *)

declare [[ML_print_depth=30]]

derive_generic (metadata) showable simple .
derive_generic (metadata) showable either .

value "print (A 3)" 
value "print (B 1 2)"
value [simp] "print (L (2::nat))"
value "print C"

(* recursive types *)

derive_generic (metadata) showable list .
derive_generic (metadata) showable tree .

value "print [1,2::nat]"
value "print (Node (3::nat) (Node 1 Leaf Leaf) (Node 2 Leaf Leaf))"

(* mutually recursive types *)

derive_generic (metadata) showable even_nat .
derive_generic (metadata) showable exp .

value "print (Odd_Succ (Even_Succ (Odd_Succ Even_Zero)))"
value [simp] "print (Sum (Factor (Const (0::nat))) (Term (Prod (Const (1::nat)) (Factor (Const (2::nat))))))"

end