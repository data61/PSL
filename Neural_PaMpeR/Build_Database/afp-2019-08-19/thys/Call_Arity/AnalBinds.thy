theory AnalBinds
imports Launchbury.Terms "Launchbury.HOLCF-Utils" Launchbury.Env
begin

locale ExpAnalysis =
  fixes exp :: "exp \<Rightarrow> 'a::cpo \<rightarrow> 'b::pcpo"
begin

fun AnalBinds :: "heap \<Rightarrow> (var \<Rightarrow> 'a\<^sub>\<bottom>) \<rightarrow> (var \<Rightarrow> 'b)"
  where "AnalBinds [] = (\<Lambda> ae. \<bottom>)"
      | "AnalBinds ((x,e)#\<Gamma>) = (\<Lambda> ae. (AnalBinds \<Gamma>\<cdot>ae)(x := fup\<cdot>(exp e)\<cdot>(ae x)))"

lemma AnalBinds_Nil_simp[simp]: "AnalBinds []\<cdot>ae = \<bottom>" by simp

lemma AnalBinds_Cons[simp]:
  "AnalBinds ((x,e)#\<Gamma>)\<cdot>ae = (AnalBinds \<Gamma>\<cdot>ae)(x := fup\<cdot>(exp e)\<cdot>(ae x))" 
  by simp

lemmas AnalBinds.simps[simp del]

lemma AnalBinds_not_there: "x \<notin> domA \<Gamma> \<Longrightarrow> (AnalBinds \<Gamma>\<cdot>ae) x = \<bottom>"
  by (induction \<Gamma> rule: AnalBinds.induct) auto
 
lemma AnalBinds_cong:
  assumes "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma>"
  shows "AnalBinds \<Gamma>\<cdot>ae = AnalBinds \<Gamma>\<cdot>ae'"
using env_restr_eqD[OF assms]
by (induction \<Gamma> rule: AnalBinds.induct) (auto split: if_splits)

lemma AnalBinds_lookup: "(AnalBinds \<Gamma>\<cdot>ae) x = (case map_of \<Gamma> x of Some e \<Rightarrow> fup\<cdot>(exp e)\<cdot>(ae x) | None \<Rightarrow> \<bottom>)"
  by (induction \<Gamma> rule: AnalBinds.induct) auto

lemma AnalBinds_delete_bot: "ae x = \<bottom> \<Longrightarrow> AnalBinds (delete x \<Gamma>)\<cdot>ae = AnalBinds \<Gamma>\<cdot>ae"
  by (auto simp add: AnalBinds_lookup split:option.split simp add: delete_conv)

lemma AnalBinds_delete_below: "AnalBinds (delete x \<Gamma>)\<cdot>ae \<sqsubseteq> AnalBinds \<Gamma>\<cdot>ae"
  by (auto intro: fun_belowI simp add: AnalBinds_lookup split:option.split)

lemma AnalBinds_delete_lookup[simp]: "(AnalBinds (delete x \<Gamma>)\<cdot>ae) x = \<bottom>"
  by (auto  simp add: AnalBinds_lookup split:option.split)

lemma AnalBinds_delete_to_fun_upd: "AnalBinds (delete x \<Gamma>)\<cdot>ae = (AnalBinds \<Gamma>\<cdot>ae)(x := \<bottom>)"
  by (auto  simp add: AnalBinds_lookup split:option.split)
 
lemma edom_AnalBinds: "edom (AnalBinds \<Gamma>\<cdot>ae) \<subseteq> domA \<Gamma> \<inter> edom ae"
  by (induction \<Gamma> rule: AnalBinds.induct) (auto  simp add: edom_def)

end

end
