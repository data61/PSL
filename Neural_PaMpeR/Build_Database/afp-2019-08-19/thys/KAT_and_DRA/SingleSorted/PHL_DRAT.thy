(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Propositional Hoare Logic\<close>

theory PHL_DRAT
  imports DRAT Kleene_Algebra.PHL_DRA PHL_KAT
begin

sublocale drat < phl: at_it_pre_dioid where alpha = t and tau = t and it = strong_iteration ..

context drat
begin

no_notation while ("while _ do _ od" [64,64] 63)

abbreviation while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while b do x od \<equiv> (b \<cdot> x)\<^sup>\<infinity> \<cdot> !b"

lemma  phl_n_while: 
  assumes "\<lbrace>n x \<cdot>  n y\<rbrace> z \<lbrace>n x\<rbrace>"
  shows "\<lbrace>n x\<rbrace> (n y \<cdot> z)\<^sup>\<infinity> \<cdot> t y \<lbrace>n x \<cdot> t y\<rbrace>"
  by (metis assms phl.ht_at_phl_while t_n_closed)

lemma phl_test_while: 
  assumes "test p" and "test b" 
  and "\<lbrace>p \<cdot> b\<rbrace> x \<lbrace>p\<rbrace>"
  shows "\<lbrace>p\<rbrace> (b \<cdot> x)\<^sup>\<infinity> \<cdot> !b \<lbrace>p \<cdot> !b\<rbrace>"
  by (metis assms phl_n_while test_double_comp_var)

lemma phl_while_syntax: 
  assumes "test p" and "test b" and "\<lbrace>p \<cdot> b\<rbrace> x \<lbrace>p\<rbrace>"
  shows "\<lbrace>p\<rbrace> while b do x od \<lbrace>p \<cdot> !b\<rbrace>"
  by (metis assms phl_test_while)

end

end

