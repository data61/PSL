(* Title:      Generalised Hoare Logic for Kleene Algebra
   Author:     Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Propositional Hoare Logic for Conway and Kleene Algebra\<close>

theory PHL_KA
  imports Kleene_Algebra

begin

(**********************************************************)

text \<open>This is a minimalist Hoare logic developed in the context of pre-dioids. In near-dioids, the sequencing rule would not be derivable.
 Iteration is modelled by a function that needs to satisfy a simulation law. 

The main assumtions on pre-dioid elements needed to derive the Hoare rules are preservation properties; an additional distributivity propery is needed
for the conditional rule. 

This Hoare logic can be instantated in various ways. It covers notions of 
finite and possibly infinite iteration. In this theory, it it specialised to Conway and Kleene algebras.\<close>

class it_pre_dioid = pre_dioid_one +
  fixes it :: "'a \<Rightarrow> 'a" 
  assumes it_simr: "y \<cdot> x \<le> x \<cdot> y \<Longrightarrow> y \<cdot> it x \<le> it x \<cdot> y"

begin

lemma phl_while:  
  assumes "p \<cdot> s \<le> s \<cdot> p \<cdot> s" and "p \<cdot> w \<le> w \<cdot> p \<cdot> w"
  and  "(p \<cdot> s) \<cdot> x \<le> x \<cdot> p"
  shows "p \<cdot> (it (s \<cdot> x) \<cdot> w)  \<le> it (s \<cdot> x) \<cdot> w \<cdot> (p \<cdot> w)"
proof -
  have "p \<cdot> s \<cdot> x \<le> s \<cdot> x \<cdot> p"
    by (metis assms(1) assms(3) mult.assoc phl_export1)
  hence "p \<cdot> it (s \<cdot> x) \<le> it (s \<cdot> x) \<cdot> p"
    by (simp add: it_simr mult.assoc)
  thus ?thesis
    using assms(2) phl_export2 by blast
qed

end

text \<open>Next we define a Hoare triple to make the format of the rules more explicit.\<close>

context pre_dioid_one
begin

abbreviation (in near_dioid) ht :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>") where
  "\<lbrace>x\<rbrace> y \<lbrace>z\<rbrace> \<equiv> x \<cdot> y \<le> y \<cdot> z" 

lemma ht_phl_skip: "\<lbrace>x\<rbrace> 1 \<lbrace>x\<rbrace>"
  by simp
  
lemma ht_phl_cons1: "x \<le> w \<Longrightarrow> \<lbrace>w\<rbrace> y \<lbrace>z\<rbrace> \<Longrightarrow> \<lbrace>x\<rbrace> y \<lbrace>z\<rbrace>"
  by (fact phl_cons1)

lemma ht_phl_cons2: "w \<le> x \<Longrightarrow> \<lbrace>z\<rbrace> y \<lbrace>w\<rbrace> \<Longrightarrow> \<lbrace>z\<rbrace> y \<lbrace>x\<rbrace>"
  by (fact phl_cons2)

lemma ht_phl_seq: "\<lbrace>p\<rbrace> x \<lbrace>r\<rbrace> \<Longrightarrow> \<lbrace>r\<rbrace> y \<lbrace>q\<rbrace> \<Longrightarrow> \<lbrace>p\<rbrace> x \<cdot> y \<lbrace>q\<rbrace>"
  by (fact phl_seq)

lemma ht_phl_cond: 
assumes "u \<cdot> v \<le> v \<cdot> u \<cdot> v" and "u \<cdot> w \<le> w \<cdot> u \<cdot> w" 
and "\<And>x y. u \<cdot> (x + y) \<le> u \<cdot> x + u \<cdot> y"
and "\<lbrace>u \<cdot> v\<rbrace> x \<lbrace>z\<rbrace>" and "\<lbrace>u \<cdot> w\<rbrace> y \<lbrace>z\<rbrace>" 
shows "\<lbrace>u\<rbrace> (v \<cdot> x + w \<cdot> y) \<lbrace>z\<rbrace>"
  using assms by (fact phl_cond)

lemma  ht_phl_export1: 
assumes "x \<cdot> y \<le> y \<cdot> x \<cdot> y"
and "\<lbrace>x \<cdot> y\<rbrace> z \<lbrace>w\<rbrace>"
shows "\<lbrace>x\<rbrace> y \<cdot> z \<lbrace>w\<rbrace>"
  using assms by (fact phl_export1)

lemma ht_phl_export2: 
assumes "z \<cdot> w \<le> w \<cdot> z \<cdot> w"
and "\<lbrace>x\<rbrace> y \<lbrace>z\<rbrace>"
shows "\<lbrace>x\<rbrace> y \<cdot> w \<lbrace>z \<cdot> w\<rbrace>"
  using assms by (fact phl_export2)

end

context it_pre_dioid begin

lemma ht_phl_while:  
assumes "p \<cdot> s \<le> s \<cdot> p \<cdot> s" and "p \<cdot> w \<le> w \<cdot> p \<cdot> w"
and  "\<lbrace>p \<cdot> s\<rbrace> x \<lbrace>p\<rbrace>"
shows "\<lbrace>p\<rbrace> it (s \<cdot> x) \<cdot> w \<lbrace>p \<cdot> w\<rbrace>"
  using assms by (fact phl_while)

end

sublocale pre_conway < phl: it_pre_dioid where it = dagger
  by standard (simp add: local.dagger_simr)

sublocale kleene_algebra < phl: it_pre_dioid where it = star ..

end
