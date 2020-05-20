theory "C-restr"
imports C "C-Meet" "HOLCF-Utils"
begin

subsubsection \<open>The demand of a $C$-function\<close>

text \<open>
The demand is the least amount of resources required to produce a non-bottom element,
if at all.
\<close>

definition demand :: "(C \<rightarrow> 'a::pcpo) \<Rightarrow> C" where
  "demand f = (if f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom> then C\<^bsup>(LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>)\<^esup> else C\<^sup>\<infinity>)"

text \<open>
Because of continuity, a non-bottom value can always be obtained with finite resources.
\<close>

lemma finite_resources_suffice:
  assumes "f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  obtains n where "f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>"
proof-
  {
  assume "\<forall>n. f\<cdot>(C\<^bsup>n\<^esup>) = \<bottom>"
  hence "f\<cdot>C\<^sup>\<infinity> \<sqsubseteq> \<bottom>"
    by (auto intro: lub_below[OF ch2ch_Rep_cfunR[OF chain_iterate]]
             simp add: Cinf_def fix_def2 contlub_cfun_arg[OF chain_iterate])
  with assms have False by simp
  }
  thus ?thesis using that by blast
qed

text \<open>
Because of monotonicity, a non-bottom value can always be obtained with more resources.
\<close>


lemma more_resources_suffice:
  assumes "f\<cdot>r \<noteq> \<bottom>" and "r \<sqsubseteq> r'"
  shows "f\<cdot>r' \<noteq> \<bottom>"
  using assms(1) monofun_cfun_arg[OF assms(2), where  f = f]
  by auto

lemma infinite_resources_suffice:
  shows "f\<cdot>r \<noteq> \<bottom> \<Longrightarrow> f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  by (erule more_resources_suffice[OF _ below_Cinf])

lemma demand_suffices:
  assumes "f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>"
  shows "f\<cdot>(demand f) \<noteq> \<bottom>"
  apply (simp add: assms demand_def)
  apply (rule finite_resources_suffice[OF assms])
  apply (rule LeastI)
  apply assumption
  done

lemma not_bot_demand:
  "f\<cdot>r \<noteq> \<bottom> \<longleftrightarrow> demand f \<noteq> C\<^sup>\<infinity> \<and> demand f \<sqsubseteq> r"
proof(intro iffI)
  assume "f\<cdot>r \<noteq> \<bottom>"
  thus "demand f \<noteq> C\<^sup>\<infinity> \<and> demand f \<sqsubseteq> r"
    apply (cases r rule:C_cases)
    apply (auto intro: Least_le simp add: demand_def dest: infinite_resources_suffice)
    done
next
  assume *: "demand f \<noteq> C\<^sup>\<infinity>  \<and> demand f \<sqsubseteq> r"
  then have "f\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>" by (auto intro: Least_le simp add: demand_def dest: infinite_resources_suffice)
  hence "f\<cdot>(demand f) \<noteq> \<bottom>" by (rule demand_suffices)
  moreover from * have "demand f \<sqsubseteq> r"..
  ultimately
  show "f\<cdot>r \<noteq> \<bottom>" by (rule more_resources_suffice)
qed

lemma infinity_bot_demand:
  "f\<cdot>C\<^sup>\<infinity> = \<bottom> \<longleftrightarrow> demand f = C\<^sup>\<infinity>"
  by (metis below_Cinf not_bot_demand)

lemma demand_suffices':
  assumes "demand f = C\<^bsup>n\<^esup>"
  shows "f\<cdot>(demand f) \<noteq> \<bottom>"
  by (metis C_eq_Cinf assms demand_suffices infinity_bot_demand)

lemma demand_Suc_Least:
  assumes [simp]: "f\<cdot>\<bottom> = \<bottom>"
  assumes "demand f \<noteq> C\<^sup>\<infinity>"
  shows "demand f = C\<^bsup>(Suc (LEAST n. f\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>))\<^esup>"
proof-
  from assms
  have "demand f = C\<^bsup>(LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>)\<^esup>" by (auto simp add: demand_def)
  also
  then obtain n where "f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>" by (metis  demand_suffices')
  hence "(LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>) = Suc (LEAST n. f\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>)"
    apply (rule Least_Suc) by simp
  finally show ?thesis.
qed

lemma demand_C_case[simp]: "demand (C_case\<cdot>f) = C \<cdot> (demand f)"
proof(cases "demand (C_case\<cdot>f) = C\<^sup>\<infinity>")
  case True
  then have "C_case\<cdot>f\<cdot>C\<^sup>\<infinity> = \<bottom>"
    by (metis infinity_bot_demand)
  with True
  show ?thesis apply auto by (metis infinity_bot_demand)
next
  case False
  hence "demand (C_case\<cdot>f) = C\<^bsup>Suc (LEAST n. (C_case\<cdot>f)\<cdot>C\<^bsup>Suc n\<^esup> \<noteq> \<bottom>)\<^esup>"
    by (rule demand_Suc_Least[OF C.case_rews(1)])
  also have "\<dots> = C\<cdot>C\<^bsup>LEAST n. f\<cdot>C\<^bsup>n\<^esup> \<noteq> \<bottom>\<^esup>" by simp
  also have "\<dots> = C\<cdot>(demand  f)"
    using False unfolding demand_def by auto
  finally show ?thesis.
qed

lemma demand_contravariant:
  assumes "f \<sqsubseteq> g"
  shows "demand g \<sqsubseteq> demand f"
proof(cases "demand f" rule:C_cases)
  fix n
  assume "demand f = C\<^bsup>n\<^esup>"
  hence "f\<cdot>(demand f) \<noteq> \<bottom>" by (metis demand_suffices')
  also note monofun_cfun_fun[OF assms]
  finally have "g\<cdot>(demand f) \<noteq> \<bottom>" by this (intro cont2cont)
  thus "demand g \<sqsubseteq> demand f" unfolding not_bot_demand by auto
qed auto

subsubsection \<open>Restricting functions with domain C\<close>

fixrec C_restr :: "C \<rightarrow> (C \<rightarrow> 'a::pcpo) \<rightarrow> (C \<rightarrow> 'a)"
  where "C_restr\<cdot>r\<cdot>f\<cdot>r' = (f\<cdot>(r \<sqinter> r'))" 

abbreviation C_restr_syn :: "(C \<rightarrow> 'a::pcpo) \<Rightarrow> C \<Rightarrow> (C \<rightarrow> 'a)" ( "_|\<^bsub>_\<^esub>" [111,110] 110)
  where "f|\<^bsub>r\<^esub> \<equiv> C_restr\<cdot>r\<cdot>f"

lemma [simp]: "\<bottom>|\<^bsub>r\<^esub> = \<bottom>" by fixrec_simp
lemma [simp]: "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> f|\<^bsub>\<bottom>\<^esub> = \<bottom>"  by fixrec_simp

lemma C_restr_C_restr[simp]: "(v|\<^bsub>r'\<^esub>)|\<^bsub>r\<^esub> = v|\<^bsub>(r' \<sqinter> r)\<^esub>"
  by (rule cfun_eqI) simp

lemma C_restr_eqD:
  assumes "f|\<^bsub>r\<^esub> = g|\<^bsub>r\<^esub>"
  assumes "r' \<sqsubseteq> r"
  shows "f\<cdot>r' = g\<cdot>r'"
by (metis C_restr.simps assms below_refl is_meetI)

lemma C_restr_eq_lower:
  assumes "f|\<^bsub>r\<^esub> = g|\<^bsub>r\<^esub>"
  assumes "r' \<sqsubseteq> r"
  shows "f|\<^bsub>r'\<^esub> = g|\<^bsub>r'\<^esub>"
by (metis C_restr_C_restr assms below_refl is_meetI)

lemma C_restr_below[intro, simp]:
  "x|\<^bsub>r\<^esub> \<sqsubseteq> x"
  apply (rule cfun_belowI)
  apply simp
  by (metis below_refl meet_below2 monofun_cfun_arg)
  

lemma C_restr_below_cong:
  "(\<And> r'. r' \<sqsubseteq> r \<Longrightarrow> f \<cdot> r' \<sqsubseteq> g \<cdot> r') \<Longrightarrow> f|\<^bsub>r\<^esub> \<sqsubseteq> g|\<^bsub>r\<^esub>"
  apply (rule cfun_belowI)
  apply simp
  by (metis below_refl meet_below1)

lemma C_restr_cong:
  "(\<And> r'. r' \<sqsubseteq> r \<Longrightarrow> f \<cdot> r' = g \<cdot> r') \<Longrightarrow> f|\<^bsub>r\<^esub> = g|\<^bsub>r\<^esub>"
  apply (intro below_antisym C_restr_below_cong )
  by (metis below_refl)+

lemma C_restr_C_cong:
  "(\<And> r'. r' \<sqsubseteq> r \<Longrightarrow> f \<cdot> (C\<cdot>r') = g \<cdot> (C\<cdot>r')) \<Longrightarrow> f\<cdot>\<bottom>=g\<cdot>\<bottom> \<Longrightarrow> f|\<^bsub>C\<cdot>r\<^esub> = g|\<^bsub>C\<cdot>r\<^esub>"
  apply (rule C_restr_cong)
  by (case_tac r', auto)

lemma C_restr_C_case[simp]:
  "(C_case\<cdot>f)|\<^bsub>C\<cdot>r\<^esub> = C_case\<cdot>(f|\<^bsub>r\<^esub>)"
  apply (rule cfun_eqI)
  apply simp
  apply (case_tac x)
  apply simp
  apply simp
  done

lemma C_restr_bot_demand:
  assumes "C\<cdot>r \<sqsubseteq> demand f"
  shows "f|\<^bsub>r\<^esub> = \<bottom>"
proof(rule cfun_eqI)
  fix r'
  have "f\<cdot>(r \<sqinter> r') = \<bottom>"
  proof(rule classical)
    have "r \<sqsubseteq> C \<cdot> r" by (rule below_C)
    also
    note assms
    also
    assume *: "f\<cdot>(r \<sqinter> r') \<noteq> \<bottom>"
    hence "demand f \<sqsubseteq> (r \<sqinter> r')" unfolding not_bot_demand by auto
    hence "demand f \<sqsubseteq> r"  by (metis below_refl meet_below1 below_trans)
    finally (below_antisym) have "r = demand f" by this (intro cont2cont)
    with assms
    have "demand f = C\<^sup>\<infinity>" by (cases "demand f" rule:C_cases) (auto simp add: iterate_Suc[symmetric] simp del: iterate_Suc)
    thus "f\<cdot>(r \<sqinter> r') = \<bottom>" by (metis not_bot_demand)
  qed
  thus "(f|\<^bsub>r\<^esub>)\<cdot>r' = \<bottom>\<cdot>r'" by simp
qed

subsubsection \<open>Restricting maps of C-ranged functions\<close>

definition env_C_restr :: "C \<rightarrow> ('var::type \<Rightarrow> (C \<rightarrow> 'a::pcpo)) \<rightarrow> ('var \<Rightarrow> (C \<rightarrow> 'a))" where
  "env_C_restr = (\<Lambda> r f.  cfun_comp\<cdot>(C_restr\<cdot>r)\<cdot>f)"

abbreviation env_C_restr_syn :: "('var::type \<Rightarrow> (C \<rightarrow> 'a::pcpo)) \<Rightarrow> C \<Rightarrow>  ('var \<Rightarrow> (C \<rightarrow> 'a))" ( "_|\<^sup>\<circ>\<^bsub>_\<^esub>" [111,110] 110)
  where "f|\<^sup>\<circ>\<^bsub>r\<^esub> \<equiv> env_C_restr\<cdot>r\<cdot>f"


lemma env_C_restr_upd[simp]: "(\<rho>(x := v))|\<^sup>\<circ>\<^bsub>r\<^esub> = (\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>)(x := v|\<^bsub>r\<^esub>)"
  unfolding env_C_restr_def by simp

lemma env_C_restr_lookup[simp]: "(\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub>) v = \<rho> v|\<^bsub>r\<^esub>"
  unfolding env_C_restr_def by simp

lemma env_C_restr_bot[simp]: " \<bottom>|\<^sup>\<circ>\<^bsub>r\<^esub> = \<bottom>"
  unfolding env_C_restr_def by auto

lemma env_C_restr_restr_below[intro]: "\<rho>|\<^sup>\<circ>\<^bsub>r\<^esub> \<sqsubseteq> \<rho>"
  by (auto intro: fun_belowI)

lemma env_C_restr_env_C_restr[simp]: "(v|\<^sup>\<circ>\<^bsub>r'\<^esub>)|\<^sup>\<circ>\<^bsub>r\<^esub> = v|\<^sup>\<circ>\<^bsub>(r' \<sqinter> r)\<^esub>"
  unfolding env_C_restr_def by auto

lemma env_C_restr_cong:
  "(\<And> x r'. r' \<sqsubseteq> r \<Longrightarrow> f x \<cdot> r' = g x \<cdot> r') \<Longrightarrow> f|\<^sup>\<circ>\<^bsub>r\<^esub> = g|\<^sup>\<circ>\<^bsub>r\<^esub>"
  unfolding env_C_restr_def
  by (rule ext) (auto intro: C_restr_cong)

end
