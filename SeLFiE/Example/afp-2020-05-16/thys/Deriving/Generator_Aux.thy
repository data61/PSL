section \<open>Shared Utilities for all Generator\<close>

text \<open>In this theory we mainly provide some Isabelle/ML infrastructure
  that is used by several generators. It consists of a uniform interface
  to access all the theorems, terms, etc.\ from the BNF package, and 
  some auxiliary functions which provide recursors on datatypes, common tactics, etc.\<close>

theory Generator_Aux
imports 
  Main
begin

ML_file \<open>bnf_access.ML\<close>
ML_file \<open>generator_aux.ML\<close>

lemma in_set_simps: 
  "x \<in> set (y # z # ys) = (x = y \<or> x \<in> set (z # ys))"
  "x \<in> set ([y]) = (x = y)"
  "x \<in> set [] = False" 
  "Ball (set []) P = True" 
  "Ball (set [x]) P = P x" 
  "Ball (set (x # y # zs)) P = (P x \<and> Ball (set (y # zs)) P)" 
  by auto
  
lemma conj_weak_cong: "a = b \<Longrightarrow> c = d \<Longrightarrow> (a \<and> c) = (b \<and> d)" by auto

lemma refl_True: "(x = x) = True" by simp

end
