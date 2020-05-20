section "Encoding"

theory Derive_Encode
imports Main "../Derive" Derive_Datatypes
begin

class encodeable =
  fixes encode :: "'a \<Rightarrow> bool list"

(* Manual instances for nat, unit, prod, and sum *)    
instantiation nat and unit:: encodeable
begin  
  fun encode_nat :: "nat \<Rightarrow> bool list" where 
  "encode_nat 0 = []" |
  "encode_nat (Suc n) = True # (encode n)"
  
  definition encode_unit: "encode (x::unit) = []"
  instance ..
end 

instantiation prod and sum :: (encodeable, encodeable) encodeable
begin
  definition encode_prod_def: "encode x = append (encode (fst x)) (encode (snd x))"
  definition encode_sum_def:  "encode x = (case x of Inl a \<Rightarrow> False # encode a
                                                   | Inr a \<Rightarrow> True # encode a)"
  instance ..
end

derive_generic encodeable simple .
derive_generic encodeable either .
  
lemma "encode (B 3 4) = [True, False, True, True, True, True, True, True, True]" by eval
lemma "encode C = [True, True]" by eval 
lemma "encode (R (3::nat)) = [True, True, True, True]" by code_simp
  
(* recursive types *) 
  
derive_generic encodeable list .
derive_generic encodeable tree .
  
lemma "encode [1,2,3,4::nat] 
  = [True, True, True, True, True, True, True, True, True, True, True, True, True, True, False]" by eval
lemma "encode (Node (3::nat) (Node 1 Leaf Leaf) (Node 2 Leaf Leaf)) 
  = [True, True, True, True, True, True, False, False, True, True, True, False, False]" by eval

(* mutually recursive types *)

derive_generic encodeable even_nat .
derive_generic encodeable exp .
   
lemma "encode (Odd_Succ (Even_Succ (Odd_Succ Even_Zero))) 
  = [True, False, True, True, False, False]" by eval 
lemma "encode (Term (Prod (Const (1::nat)) (Factor (Const (2::nat)))))
  = [False, False, True, False, True, True, True, False, True, True, False, False, True, True, False, True, True]" 
  by code_simp    

end