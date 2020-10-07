(*
  File: Partial_Equiv_Rel.thy
  Author: Bohua Zhan
*)

section \<open>Partial equivalence relation\<close>

theory Partial_Equiv_Rel
  imports "Auto2_HOL.Auto2_Main"
begin
  
text \<open>
  Partial equivalence relations, following theory
  Lib/Partial\_Equivalence\_Relation in \cite{Collections-AFP}.
\<close>

definition part_equiv :: "('a \<times> 'a) set \<Rightarrow> bool" where [rewrite]:
  "part_equiv R \<longleftrightarrow> sym R \<and> trans R"

lemma part_equivI [forward]: "sym R \<Longrightarrow> trans R \<Longrightarrow> part_equiv R" by auto2
lemma part_equivD1 [forward]: "part_equiv R \<Longrightarrow> sym R" by auto2
lemma part_equivD2 [forward]: "part_equiv R \<Longrightarrow> trans R" by auto2
setup \<open>del_prfstep_thm_eqforward @{thm part_equiv_def}\<close>

subsection \<open>Combining two elements in a partial equivalence relation\<close>

definition per_union :: "('a \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set" where [rewrite]:
  "per_union R a b = R \<union> { (x,y). (x,a)\<in>R \<and> (b,y)\<in>R } \<union> { (x,y). (x,b)\<in>R \<and> (a,y)\<in>R }"

lemma per_union_memI1 [backward]:
  "(x, y) \<in> R \<Longrightarrow> (x, y) \<in> per_union R a b" by (simp add: per_union_def)
setup \<open>add_forward_prfstep_cond @{thm per_union_memI1} [with_term "per_union ?R ?a ?b"]\<close>

lemma per_union_memI2 [backward]:
  "(x, a) \<in> R \<Longrightarrow> (b, y) \<in> R \<Longrightarrow> (x, y) \<in> per_union R a b" by (simp add: per_union_def)

lemma per_union_memI3 [backward]:
  "(x, b) \<in> R \<Longrightarrow> (a, y) \<in> R \<Longrightarrow> (x, y) \<in> per_union R a b" by (simp add: per_union_def)

lemma per_union_memD:
  "(x, y) \<in> per_union R a b \<Longrightarrow> (x, y) \<in> R \<or> ((x, a) \<in> R \<and> (b, y) \<in> R) \<or> ((x, b) \<in> R \<and> (a, y) \<in> R)"
  by (simp add: per_union_def)
setup \<open>add_forward_prfstep_cond @{thm per_union_memD} [with_cond "?x \<noteq> ?y", with_filt (order_filter "x" "y")]\<close>
setup \<open>del_prfstep_thm @{thm per_union_def}\<close>

lemma per_union_is_trans [forward]:
  "trans R \<Longrightarrow> trans (per_union R a b)" by auto2

lemma per_union_is_part_equiv [forward]:
  "part_equiv R \<Longrightarrow> part_equiv (per_union R a b)" by auto2

end
