(*  
  Title:    Libraries.thy
  Author:   Manuel Eberl, TU München

  Definition of lotteries on a set. (Essentially just restricting PMFs to a carrier set)
*)

section \<open>Auxiliary facts about PMFs\<close>

theory Lotteries
  imports Complex_Main "HOL-Probability.Probability"
begin

text \<open>The type of lotteries (a probability mass function)\<close>
type_synonym 'alt lottery = "'alt pmf"

definition lotteries_on :: "'a set \<Rightarrow> 'a lottery set" where
  "lotteries_on A = {p. set_pmf p \<subseteq> A}"

lemma pmf_of_set_lottery:
  "A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> pmf_of_set A \<in> lotteries_on B"
  unfolding lotteries_on_def by auto

lemma pmf_of_list_lottery: 
  "pmf_of_list_wf xs \<Longrightarrow> set (map fst xs) \<subseteq> A \<Longrightarrow> pmf_of_list xs \<in> lotteries_on A"
  using set_pmf_of_list[of xs] by (auto simp: lotteries_on_def)

lemma return_pmf_in_lotteries_on [simp,intro]: 
  "x \<in> A \<Longrightarrow> return_pmf x \<in> lotteries_on A"
  by (simp add: lotteries_on_def)

end
