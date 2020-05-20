theory Elections
imports Preference_Profiles
begin

text \<open>
  An election consists of a finite set of agents and a finite non-empty 
  set of alternatives.
\<close>
locale election = 
  fixes agents :: "'agent set" and alts :: "'alt set"
  assumes finite_agents [simp, intro]: "finite agents"
  assumes finite_alts [simp, intro]: "finite alts"
  assumes nonempty_agents [simp]: "agents \<noteq> {}"
  assumes nonempty_alts [simp]: "alts \<noteq> {}"
begin

abbreviation "is_pref_profile \<equiv> pref_profile_wf agents alts"

lemma finite_total_preorder_on_iff' [simp]:
  "finite_total_preorder_on alts R \<longleftrightarrow> total_preorder_on alts R"
  by (simp add: finite_total_preorder_on_iff)

lemma pref_profile_wfI' [intro?]:
  "(\<And>i. i \<in> agents \<Longrightarrow> total_preorder_on alts (R i)) \<Longrightarrow>
   (\<And>i. i \<notin> agents \<Longrightarrow> R i = (\<lambda>_ _. False)) \<Longrightarrow> is_pref_profile R"
  by (simp add: pref_profile_wf_def)

lemma is_pref_profile_update [simp,intro]:
  assumes "is_pref_profile R" "total_preorder_on alts Ri'" "i \<in> agents"
  shows   "is_pref_profile (R(i := Ri'))"
  using assms by (auto intro!: pref_profile_wf.wf_update)

lemma election [simp,intro]: "election agents alts"
  by (rule election_axioms)


context
  fixes R assumes R: "total_preorder_on alts R"
begin

interpretation R: total_preorder_on alts R by fact

lemma Max_wrt_prefs_finite: "finite (Max_wrt R)"
  unfolding R.Max_wrt_preorder by simp

lemma Max_wrt_prefs_nonempty: "Max_wrt R \<noteq> {}"
  using R.Max_wrt_nonempty by simp

lemma maximal_imp_preferred:
  "x \<in> alts \<Longrightarrow> Max_wrt R \<subseteq> preferred_alts R x"
  using R.total
  by (auto simp: R.Max_wrt_total_preorder preferred_alts_def strongly_preferred_def)

end

end

end
