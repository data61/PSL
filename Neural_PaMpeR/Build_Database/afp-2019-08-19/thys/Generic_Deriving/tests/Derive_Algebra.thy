section "Algebraic Classes"

theory Derive_Algebra
imports Main "../Derive" Derive_Datatypes
begin

class semigroup = 
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
(*  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)" *)
    
class monoidl = semigroup +
fixes neutral :: 'a ("\<one>")
(* assumes neutl : "\<one> \<otimes> x = x" *)    
  
class group = monoidl +
  fixes inverse :: "'a \<Rightarrow> 'a"
(* assumes invl: "x\<div> \<otimes> x = \<one>" *)
    
(* Manual instances for nat, unit, prod, and sum *)    
instantiation nat and unit:: semigroup
begin  
  definition mult_nat : "mult (x::nat) y = x + y"
  definition mult_unit_def: "mult (x::unit) y = x"
  instance ..
end 
instantiation nat and unit:: monoidl
begin  
  definition neutral_nat : "neutral = (0::nat)"
  definition neutral_unit_def: "neutral = ()"
  instance ..
end   
  
instantiation nat and unit:: group
begin  
  definition inverse_nat : "inverse (i::nat) = \<one> - i"
  definition inverse_unit_def: "inverse u = ()"
  instance ..
end   

instantiation prod and sum :: (semigroup, semigroup) semigroup
begin
  definition mult_prod_def: "x \<otimes> y = (fst x \<otimes> fst y, snd x \<otimes> snd y)"
  definition mult_sum_def: "x \<otimes> y = (case x of Inl a \<Rightarrow> (case y of Inl b \<Rightarrow> Inl (a \<otimes> b) | Inr b \<Rightarrow> Inl a)
                                             | Inr a \<Rightarrow> (case y of Inl b \<Rightarrow> Inr a | Inr b \<Rightarrow> Inr (a \<otimes> b)))"
  instance ..
end
  
instantiation prod and sum :: (monoidl, monoidl) monoidl
begin
  definition neutral_prod_def: "neutral = (neutral,neutral)"
  definition neutral_sum_def: "neutral = Inl neutral"
  instance ..
end 
  
instantiation prod and sum :: (group, group) group
begin
  definition inverse_prod_def: "inverse p = (inverse (fst p), inverse (snd p))"
  definition inverse_sum_def: "inverse x = (case x of Inl a \<Rightarrow> (Inl (inverse a)) 
                                                    | Inr b \<Rightarrow> Inr (inverse b))"
  instance ..
end    
    
(* Simple test *)  
  
derive_generic semigroup simple .
derive_generic monoidl simple .
derive_generic group simple .
  
lemma "(B \<one> 6) \<otimes> (B 4 5) = B 4 11" by eval
lemma "(A 2) \<otimes> (A 3) = A 5" by eval
lemma "(B \<one> 6) \<otimes> \<one> = B 0 6" by eval
  
(* type with parameter *)
  
derive_generic group either .  

lemma "(L 3) \<otimes> ((L 4)::(nat,nat) either) = L 7" by eval
lemma "(R (2::nat)) \<otimes> (L (3::nat)) = R 2" by eval
  
(* recursive types *) 

derive_generic semigroup list .
derive_generic monoidl list .
derive_generic group list .
derive_generic semigroup tree .
derive_generic monoidl tree .
derive_generic group tree .
  
lemma "[1,2,3,4::nat] \<otimes> [1,2,3] = [2,4,6,4]" by eval
lemma "inverse [1,2,3::nat] = [0,0,0]" by eval

(* mutually recursive types *)

derive_generic semigroup even_nat .
derive_generic monoidl even_nat .
derive_generic group even_nat .
derive_generic semigroup exp .

(* instantiate monoidl manually *)  
instantiation exp and trm and fct  :: (monoidl,monoidl) monoidl 
begin  
  definition neutral_fct where "neutral_fct = Const neutral"
  definition neutral_trm where "neutral_trm = Factor neutral"
  definition neutral_exp where "neutral_exp = Term neutral"
  instance ..
end     

(* Manually defined instances need to be added to the theory context *)
setup \<open>
(Derive.add_inst_info \<^class>\<open>monoidl\<close> \<^type_name>\<open>fct\<close> [@{thm neutral_fct_def}]) #>
(Derive.add_inst_info \<^class>\<open>monoidl\<close> \<^type_name>\<open>trm\<close> [@{thm neutral_trm_def}]) #>
(Derive.add_inst_info \<^class>\<open>monoidl\<close> \<^type_name>\<open>exp\<close> [@{thm neutral_exp_def}])
\<close>

derive_generic group exp .
   
lemma "(Odd_Succ (Even_Succ (Odd_Succ Even_Zero))) \<otimes> (Odd_Succ Even_Zero) 
       = Odd_Succ (Even_Succ (Odd_Succ Even_Zero))" by eval
lemma "inverse (Odd_Succ Even_Zero) = Odd_Succ Even_Zero" by eval
lemma "(Term (Prod ((Const 1)::(nat, nat) fct) (Factor (Const (2::nat))))) 
    \<otimes> (Term (Prod (Const (2::nat)) (Factor ((Const 2)::(nat, nat) fct))))
    = Term (Prod (Const 3) (Factor (Const 4)))" by eval   


end