theory ArityAnalysisAbinds
imports ArityAnalysisSig
begin

context ArityAnalysis
begin

subsubsection \<open>Lifting arity analysis to recursive groups\<close>

definition ABind :: "var \<Rightarrow> exp \<Rightarrow> (AEnv \<rightarrow> AEnv)"
  where "ABind v e = (\<Lambda> ae. fup\<cdot>(Aexp e)\<cdot>(ae v))"

lemma ABind_eq[simp]: "ABind v e \<cdot> ae = \<A>\<^sup>\<bottom>\<^bsub>ae v\<^esub> e"
  unfolding ABind_def by (simp add: cont_fun)

fun ABinds :: "heap \<Rightarrow> (AEnv \<rightarrow> AEnv)"
  where "ABinds [] = \<bottom>"
     |  "ABinds ((v,e)#binds) = ABind v e \<squnion> ABinds (delete v binds)"

lemma ABinds_strict[simp]: "ABinds \<Gamma>\<cdot>\<bottom>=\<bottom>"
  by (induct \<Gamma> rule: ABinds.induct) auto

lemma Abinds_reorder1: "map_of \<Gamma> v = Some e \<Longrightarrow> ABinds \<Gamma> = ABind v e \<squnion> ABinds (delete v \<Gamma>)"
  by (induction \<Gamma> rule: ABinds.induct) (auto simp add: delete_twist)

lemma ABind_below_ABinds: "map_of \<Gamma> v = Some e \<Longrightarrow> ABind v e \<sqsubseteq> ABinds \<Gamma>"
  by (metis "HOLCF-Join-Classes.join_above1" ArityAnalysis.Abinds_reorder1)

lemma Abinds_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> ABinds \<Gamma> = ABinds \<Delta>"
proof (induction  \<Gamma> arbitrary: \<Delta> rule: ABinds.induct)
  case 1 thus ?case by simp
next
  case (2 v e \<Gamma> \<Delta>)
  from \<open>map_of ((v, e) # \<Gamma>) = map_of \<Delta>\<close>
  have "(map_of ((v, e) # \<Gamma>))(v := None) = (map_of \<Delta>)(v := None)" by simp
  hence "map_of (delete v \<Gamma>) = map_of (delete v \<Delta>)" unfolding delete_set_none by simp
  hence "ABinds (delete v \<Gamma>) = ABinds (delete v \<Delta>)" by (rule 2)
  moreover
  from \<open>map_of ((v, e) # \<Gamma>) = map_of \<Delta>\<close>
  have "map_of \<Delta> v = Some e" by (metis map_of_Cons_code(2))
  hence "ABinds \<Delta> = ABind v e \<squnion> ABinds (delete v \<Delta>)" by (rule Abinds_reorder1)
  ultimately
  show ?case by auto
qed

(*
lemma ABinds_above_arg: "ae \<sqsubseteq> ABinds \<Gamma> \<cdot> ae"
proof (induction rule:ABinds.induct)
  show "\<bottom> \<sqsubseteq> ABinds []\<cdot>ae" by auto
next
  fix v e \<Gamma>
  assume assm: "ae \<sqsubseteq> ABinds (delete v \<Gamma>)\<cdot>ae"
  also have "\<dots> \<sqsubseteq> ABinds ((v, e) # \<Gamma>)\<cdot>ae"  by auto
  finally show "ae \<sqsubseteq> ABinds ((v, e) # \<Gamma>)\<cdot>ae" by this simp
qed
*)

lemma Abinds_env_cong: "(\<And> x. x\<in>domA \<Delta> \<Longrightarrow> ae x = ae' x)  \<Longrightarrow>  ABinds \<Delta>\<cdot>ae = ABinds \<Delta>\<cdot>ae'"
  by (induct \<Delta> rule: ABinds.induct) auto

lemma Abinds_env_restr_cong: " ae f|` domA \<Delta> = ae' f|` domA \<Delta> \<Longrightarrow>  ABinds \<Delta>\<cdot>ae = ABinds \<Delta>\<cdot>ae'"
  by (rule Abinds_env_cong) (metis env_restr_eqD)

lemma ABinds_env_restr[simp]: "ABinds \<Delta>\<cdot>(ae f|` domA \<Delta>) = ABinds \<Delta>\<cdot>ae"
  by (rule Abinds_env_restr_cong) simp

lemma Abinds_join_fresh: "ae' ` (domA \<Delta>) \<subseteq> {\<bottom>} \<Longrightarrow>  ABinds \<Delta>\<cdot>(ae \<squnion> ae') = (ABinds \<Delta>\<cdot>ae)"
  by (rule Abinds_env_cong) auto

lemma ABinds_delete_bot: "ae x = \<bottom> \<Longrightarrow> ABinds (delete x \<Gamma>)\<cdot>ae = ABinds \<Gamma>\<cdot>ae"
  by (induction \<Gamma> rule: ABinds.induct) (auto simp add: delete_twist)

lemma ABinds_restr_fresh:
  assumes "atom ` S \<sharp>* \<Gamma>"
  shows "ABinds \<Gamma>\<cdot>ae f|` (- S) = ABinds \<Gamma>\<cdot>(ae  f|` (- S)) f|` (- S)"
  using assms
  apply (induction \<Gamma> rule:ABinds.induct)
  apply simp
  apply (auto simp del: fun_meet_simp simp add: env_restr_join fresh_star_Pair fresh_star_Cons fresh_star_delete)
  apply (subst lookup_env_restr)
  apply (metis (no_types, hide_lams) ComplI fresh_at_base(2) fresh_star_def imageI)
  apply simp
  done

lemma ABinds_restr:
  assumes "domA \<Gamma> \<subseteq> S"
  shows "ABinds \<Gamma>\<cdot>ae f|` S = ABinds \<Gamma>\<cdot>(ae  f|` S) f|` S"
  using assms
  by (induction \<Gamma> rule:ABinds.induct) (fastforce simp del: fun_meet_simp simp add: env_restr_join)+

lemma ABinds_restr_subst:
  assumes "\<And> x' e a. (x',e) \<in> set \<Gamma> \<Longrightarrow> Aexp e[x::=y]\<cdot>a f|` S = Aexp e\<cdot>a f|` S"
  assumes "x \<notin> S"
  assumes "y \<notin> S"
  assumes "domA \<Gamma> \<subseteq> S"
  shows "ABinds \<Gamma>[x::h=y]\<cdot>ae f|` S = ABinds \<Gamma>\<cdot>(ae  f|` S) f|` S"
  using assms
  apply (induction \<Gamma> rule:ABinds.induct)
  apply (auto simp del: fun_meet_simp join_comm simp add: env_restr_join)
  apply (rule arg_cong2[where f = join])
  apply (case_tac "ae v")
  apply (auto dest:  subsetD[OF set_delete_subset])
  done

lemma Abinds_append_disjoint: "domA \<Delta> \<inter> domA \<Gamma> = {} \<Longrightarrow>  ABinds (\<Delta> @ \<Gamma>)\<cdot>ae = ABinds \<Delta>\<cdot>ae \<squnion> ABinds \<Gamma>\<cdot>ae"
proof (induct \<Delta> rule: ABinds.induct)
  case 1 thus ?case by simp
next
  case (2 v e \<Delta>)
  from 2(2)
  have "v \<notin> domA \<Gamma>" and  "domA (delete v \<Delta>) \<inter> domA \<Gamma> = {}" by auto
  from 2(1)[OF this(2)]
  have "ABinds (delete v \<Delta> @ \<Gamma>)\<cdot>ae = ABinds (delete v \<Delta>)\<cdot>ae \<squnion> ABinds \<Gamma>\<cdot>ae".
  moreover
  have "delete v \<Gamma> = \<Gamma>" by (metis \<open>v \<notin> domA \<Gamma>\<close> delete_not_domA)
  ultimately
  show " ABinds (((v, e) # \<Delta>) @ \<Gamma>)\<cdot>ae = ABinds ((v, e) # \<Delta>)\<cdot>ae \<squnion> ABinds \<Gamma>\<cdot>ae"
    by auto
qed

lemma ABinds_restr_subset: "S \<subseteq> S' \<Longrightarrow> ABinds (restrictA S \<Gamma>)\<cdot>ae \<sqsubseteq> ABinds (restrictA S' \<Gamma>)\<cdot>ae"
  by (induct \<Gamma> rule: ABinds.induct)
     (auto simp add: join_below_iff  restr_delete_twist intro: below_trans[OF _ join_above2])

lemma ABinds_restrict_edom: "ABinds (restrictA (edom ae) \<Gamma>)\<cdot>ae = ABinds \<Gamma>\<cdot>ae"
  by (induct \<Gamma> rule: ABinds.induct) (auto simp add: edom_def restr_delete_twist)
  
lemma ABinds_restrict_below: "ABinds (restrictA S \<Gamma>)\<cdot>ae \<sqsubseteq> ABinds \<Gamma>\<cdot>ae"
  by (induct \<Gamma> rule: ABinds.induct)
     (auto simp add: join_below_iff  restr_delete_twist intro: below_trans[OF _ join_above2] simp del: fun_meet_simp join_comm)

lemma ABinds_delete_below: "ABinds (delete x \<Gamma>)\<cdot>ae \<sqsubseteq> ABinds \<Gamma>\<cdot>ae"
  by (induct \<Gamma> rule: ABinds.induct)
     (auto simp add: join_below_iff   delete_twist[where x = x] elim: below_trans simp del: fun_meet_simp)
end

lemma ABind_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.ABind Aexp v e) = ArityAnalysis.ABind (\<pi> \<bullet> Aexp) (\<pi> \<bullet> v) (\<pi> \<bullet> e)"
  apply (rule cfun_eqvtI)
  unfolding ArityAnalysis.ABind_eq
  by perm_simp rule

lemma ABinds_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.ABinds Aexp \<Gamma>) = ArityAnalysis.ABinds (\<pi> \<bullet> Aexp) (\<pi> \<bullet> \<Gamma>)"
  apply (rule cfun_eqvtI)
  apply (induction \<Gamma> rule: ArityAnalysis.ABinds.induct)
  apply (simp add: ArityAnalysis.ABinds.simps)
  apply (simp add: ArityAnalysis.ABinds.simps)
  apply perm_simp
  apply simp
  done

lemma Abinds_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> aexp1 e = aexp2 e) ; heap1 = heap2 \<rbrakk>
      \<Longrightarrow> ArityAnalysis.ABinds aexp1 heap1 = ArityAnalysis.ABinds aexp2 heap2"    
proof (induction heap1 arbitrary:heap2 rule:ArityAnalysis.ABinds.induct)
  case 1
  thus ?case by (auto simp add: ArityAnalysis.ABinds.simps)
next
  case prems: (2 v e as heap2)
  have "snd ` set (delete v as) \<subseteq> snd ` set as" by (rule dom_delete_subset)
  also have "\<dots> \<subseteq> snd `set ((v, e) # as)" by auto
  also note prems(3)
  finally
  have "(\<And>e. e \<in> snd ` set (delete v as) \<Longrightarrow> aexp1 e = aexp2 e)" by -(rule prems, auto)
  from prems prems(1)[OF this refl] show ?case
    by (auto simp add: ArityAnalysis.ABinds.simps ArityAnalysis.ABind_def)
qed

context EdomArityAnalysis
begin
  lemma fup_Aexp_lookup_fresh: "atom v \<sharp> e \<Longrightarrow> (fup\<cdot>(Aexp e)\<cdot>a) v = \<bottom>"
    by (cases a) auto
  
  lemma edom_AnalBinds: "edom (ABinds \<Gamma>\<cdot>ae) \<subseteq> fv \<Gamma>"
    by (induction \<Gamma> rule: ABinds.induct)
       (auto simp del: fun_meet_simp dest: subsetD[OF fup_Aexp_edom] dest: subsetD[OF fv_delete_subset])
end 

end
