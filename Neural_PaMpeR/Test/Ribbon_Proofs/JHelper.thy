section {* General purpose definitions and lemmas *}

theory JHelper imports
  Main
begin

lemma Collect_iff: 
  "a \<in> {x . P x} \<equiv> P a"
by auto

lemma diff_diff_eq:
  assumes "C \<subseteq> B"
  shows "(A - C) - (B - C) = A - B"
using assms by auto

lemma nth_in_set:
  "\<lbrakk> i < length xs ; xs ! i = x \<rbrakk> \<Longrightarrow> x \<in> set xs" by auto

lemma disjI [intro]:
  assumes "\<not> P \<Longrightarrow> Q"
  shows "P \<or> Q"
using assms by auto

lemma empty_eq_Plus_conv: 
  "({} = A <+> B) = (A = {} \<and> B = {})"
by auto

subsection {* Projection functions on triples *}

definition fst3 :: "'a \<times> 'b \<times> 'c \<Rightarrow> 'a"
where "fst3 \<equiv> fst"

definition snd3 :: "'a \<times> 'b \<times> 'c \<Rightarrow> 'b"
where "snd3 \<equiv> fst \<circ> snd"

definition thd3 :: "'a \<times> 'b \<times> 'c \<Rightarrow> 'c"
where "thd3 \<equiv> snd \<circ> snd"

lemma fst3_simp: 
  "\<And>a b c. fst3 (a,b,c) = a" 
by (auto simp add: fst3_def)

lemma snd3_simp: 
  "\<And>a b c. snd3 (a,b,c) = b" 
by (auto simp add: snd3_def)

lemma thd3_simp: 
  "\<And>a b c. thd3 (a,b,c) = c" 
by (auto simp add: thd3_def)

lemma tripleI:
  fixes T U
  assumes "fst3 T = fst3 U" 
      and "snd3 T = snd3 U" 
      and "thd3 T = thd3 U" 
  shows "T = U" 
by (metis assms fst3_def snd3_def thd3_def o_def surjective_pairing)

end
