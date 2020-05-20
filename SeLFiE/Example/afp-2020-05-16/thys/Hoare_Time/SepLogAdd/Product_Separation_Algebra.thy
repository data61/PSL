theory Product_Separation_Algebra
imports "Separation_Algebra.Separation_Algebra"
begin                 
   
instantiation "prod" :: (sep_algebra, sep_algebra) sep_algebra
begin
 
definition
  zero_prod_def: "0 \<equiv> (0, 0)"

definition
  plus_prod_def: "m1 + m2 \<equiv> (fst m1 + fst m2 , snd m1 + snd m2) "

definition
  sep_disj_prod_def: "sep_disj m1 m2 \<equiv> sep_disj (fst m1) (fst m2) \<and> sep_disj (snd m1) (snd m2)"

instance
  apply standard  unfolding sep_disj_prod_def zero_prod_def plus_prod_def 
  subgoal by auto
  subgoal by (auto simp: sep_disj_commuteI) 
  subgoal by (auto ) 
  subgoal using sep_add_commute by metis
  subgoal by (auto simp: sep_add_assoc)   
  subgoal apply auto  using sep_disj_addD1 by metis+
  subgoal apply auto using sep_disj_addI1  apply auto done
  done
  
end
   
lemma sep_disj_prod_commute[simp]: "(ps, 0) ## (0, n)"   "(0, n) ## (ps, 0)" unfolding sep_disj_prod_def by auto 

lemma sep_disj_prod_conv[simp]: "(a, x) ## (b, y) = (a##b \<and> x##y)" unfolding sep_disj_prod_def by auto
    
lemma sep_plus_prod_conv[simp]: "(ps, n) + (ps', n') = (ps + ps', n + n')" unfolding plus_prod_def by auto
  
  
lemma
  fixes h :: "('a::sep_algebra) * ('b::sep_algebra)"
  shows "((%(a,b). P a \<and> b = 0) ** (%(a,b). a = 0 \<and> Q b)) =
   (%(a,b). P a \<and> Q b)" unfolding sep_conj_def sep_disj_prod_def plus_prod_def
  apply auto apply(rule ext) apply auto by force
      
instantiation nat :: sep_algebra
begin

definition
  sep_disj_nat_def[simp]: "sep_disj (m1::nat) m2 \<equiv> True"
 
instance
  apply standard by(auto) 
end
  
(* examples *)
   
(* now nat can be used as a separation algebra *)
lemma
  fixes h :: "nat"
  shows "(P ** Q ** H) h = (Q ** H ** P) h"
  by (simp add: sep_conj_ac)
    
(* and any pair of separation algebras also is *)    
lemma
  fixes h :: "('a::sep_algebra) * ('b::sep_algebra)"
  shows "(P ** Q ** H) h = (Q ** H ** P) h"
  by (simp add: sep_conj_ac)

lemma
  fixes h :: "nat * nat"
  shows "(P ** Q ** H) h = (Q ** H ** P) h"
  by (simp add: sep_conj_ac)
        
end