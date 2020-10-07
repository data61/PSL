theory Acceptance
imports "Sequence_LTL"
begin

  type_synonym 'a pred = "'a \<Rightarrow> bool"
  type_synonym 'a rabin = "'a pred \<times> 'a pred"
  type_synonym 'a gen = "'a list"
  type_synonym 'a degen = "'a \<times> nat"

  definition rabin :: "'a rabin \<Rightarrow> 'a stream pred" where
    "rabin \<equiv> \<lambda> (I, F) w. infs I w \<and> fins F w"

  lemma rabin[intro]:
    assumes "IF = (I, F)" "infs I w" "fins F w"
    shows "rabin IF w"
    using assms unfolding rabin_def by auto
  lemma rabin_elim[elim]:
    assumes "rabin IF w"
    obtains I F
    where "IF = (I, F)" "infs I w" "fins F w"
    using assms unfolding rabin_def by auto

  definition gen :: "('a \<Rightarrow> 'b pred) \<Rightarrow> ('a gen \<Rightarrow> 'b pred)" where
    "gen P xs w \<equiv> \<forall> x \<in> set xs. P x w"

  lemma gen[intro]:
    assumes "\<And> x. x \<in> set xs \<Longrightarrow> P x w"
    shows "gen P xs w"
    using assms unfolding gen_def by auto
  lemma gen_elim[elim]:
    assumes "gen P xs w"
    obtains "\<And> x. x \<in> set xs \<Longrightarrow> P x w"
    using assms unfolding gen_def by auto

  definition cogen :: "('a \<Rightarrow> 'b pred) \<Rightarrow> ('a gen \<Rightarrow> 'b pred)" where
    "cogen P xs w \<equiv> \<exists> x \<in> set xs. P x w"

  lemma cogen[intro]:
    assumes "x \<in> set xs" "P x w"
    shows "cogen P xs w"
    using assms unfolding cogen_def by auto
  lemma cogen_elim[elim]:
    assumes "cogen P xs w"
    obtains x
    where "x \<in> set xs" "P x w"
    using assms unfolding cogen_def by auto

end