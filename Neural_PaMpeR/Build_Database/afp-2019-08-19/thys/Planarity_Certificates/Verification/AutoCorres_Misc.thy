theory AutoCorres_Misc imports
  "../l4v/lib/OptionMonadWP"
begin

section \<open>Auxilliary Lemmas for Autocorres\<close>

subsection \<open>Option monad\<close>

definition owhile_inv :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('s,'a) lookup) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 'a rel \<Rightarrow> ('s,'a) lookup"   where
 "owhile_inv c b a I R \<equiv> owhile c b a"

lemma owhile_unfold: "owhile C B r s = ocondition (C r) (B r |>> owhile C B) (oreturn r) s"
  by (auto simp: ocondition_def obind_def oreturn_def owhile_def option_while_simps split: option.split)

lemma ovalidNF_owhile:
  assumes "\<And>s. P r s \<Longrightarrow> I r s"
    and "\<And>r s. ovalidNF (\<lambda>s'. I r s' \<and> C r s' \<and> s' = s) (B r) (\<lambda>r' s'. I r' s' \<and> (r', r) \<in> R)"
    and "wf R"
    and "\<And>r s. I r s \<Longrightarrow> \<not> C r s \<Longrightarrow> Q r s"
  shows "ovalidNF (P r) (OptionMonad.owhile C B r) Q"
  unfolding ovalidNF_def
proof (intro allI impI)
  fix s assume "P r s"
  then have "I r s" by fact
  moreover note \<open>wf R\<close>
  moreover have "\<And>r r'. I r s \<Longrightarrow> C r s \<Longrightarrow> B r s = Some r' \<Longrightarrow> (r', r) \<in> R"
    using assms(2) unfolding ovalidNF_def by fastforce
  moreover have "\<And>r r'. I r s \<Longrightarrow> C r s \<Longrightarrow> B r s = Some r' \<Longrightarrow> I r' s"
    using assms(2) unfolding ovalidNF_def by blast
  moreover have "\<And>r. I r s \<Longrightarrow> C r s \<Longrightarrow> B r s = None \<Longrightarrow>
      None \<noteq> None \<and> (\<forall>r'. None = Some r' \<longrightarrow> Q r' s)"
    using assms(2) unfolding ovalidNF_def by blast
  moreover have "\<And>r. I r s \<Longrightarrow> \<not> C r s \<Longrightarrow> Some r \<noteq> None \<and> (\<forall>r'. Some r = Some r' \<longrightarrow> Q r' s)"
    using assms(4) unfolding ovalidNF_def by blast
  ultimately
  show "owhile C B r s \<noteq> None \<and> (\<forall>r'. owhile C B r s = Some r' \<longrightarrow> Q r' s)"
    by (rule owhile_rule[where I=I])
qed

lemma ovalidNF_owhile_inv[wp]:
  assumes "\<And>r s. ovalidNF (\<lambda>s'. I r s' \<and> C r s' \<and> s' = s) (B r) (\<lambda>r' s'. I r' s' \<and> (r', r) \<in> R)"
    and "wf R"
    and "\<And>r s. I r s \<Longrightarrow> \<not> C r s \<Longrightarrow> Q r s"
  shows "ovalidNF (I r) (owhile_inv C B r I R) Q"
  unfolding owhile_inv_def using _ assms by (rule ovalidNF_owhile)



end

