theory Acceptance
imports Sequence_LTL
begin

  type_synonym 'a pred = "'a \<Rightarrow> bool"
  type_synonym 'a rabin = "'a pred \<times> 'a pred"
  type_synonym 'a gen = "'a list"

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
    "gen P cs w \<equiv> \<forall> c \<in> set cs. P c w"

  lemma gen[intro]:
    assumes "\<And> c. c \<in> set cs \<Longrightarrow> P c w"
    shows "gen P cs w"
    using assms unfolding gen_def by auto
  lemma gen_elim[elim]:
    assumes "gen P cs w"
    obtains "\<And> c. c \<in> set cs \<Longrightarrow> P c w"
    using assms unfolding gen_def by auto

  definition cogen :: "('a \<Rightarrow> 'b pred) \<Rightarrow> ('a gen \<Rightarrow> 'b pred)" where
    "cogen P cs w \<equiv> \<exists> c \<in> set cs. P c w"

  lemma cogen[intro]:
    assumes "c \<in> set cs" "P c w"
    shows "cogen P cs w"
    using assms unfolding cogen_def by auto
  lemma cogen_elim[elim]:
    assumes "cogen P cs w"
    obtains c
    where "c \<in> set cs" "P c w"
    using assms unfolding cogen_def by auto

  lemma cogen_alt_def: "cogen P cs w \<longleftrightarrow> \<not> gen (\<lambda> c w. Not (P c w)) cs w" by auto

end