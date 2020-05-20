theory NoCardinalityAnalysis
imports CardinalityAnalysisSpec ArityAnalysisStack
begin

locale NoCardinalityAnalysis = ArityAnalysisLetSafe +
  assumes Aheap_thunk: "x \<in> thunks \<Gamma> \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
begin

definition a2c :: "Arity\<^sub>\<bottom> \<rightarrow> two" where "a2c = (\<Lambda> a. if a \<sqsubseteq> \<bottom> then \<bottom> else many)"
lemma a2c_simp: "a2c\<cdot>a = (if a \<sqsubseteq> \<bottom> then \<bottom> else many)"
  unfolding a2c_def by (rule beta_cfun[OF cont_if_else_above]) auto


lemma a2c_eqvt[eqvt]: "\<pi> \<bullet> a2c = a2c"
  unfolding a2c_def
  apply perm_simp
  apply (rule Abs_cfun_eqvt)
  apply (rule cont_if_else_above)
  apply auto
  done

definition ae2ce :: "AEnv \<Rightarrow> (var \<Rightarrow> two)" where "ae2ce ae x = a2c\<cdot>(ae x)"

lemma ae2ce_cont: "cont ae2ce"
  by (auto simp add: ae2ce_def) 
lemmas cont_compose[OF ae2ce_cont, cont2cont, simp]

lemma ae2ce_eqvt[eqvt]: "\<pi> \<bullet> ae2ce ae x = ae2ce (\<pi> \<bullet> ae) (\<pi> \<bullet> x)"
  unfolding ae2ce_def by perm_simp rule

lemma ae2ce_to_env_restr: "ae2ce ae = (\<lambda>_ . many) f|` edom ae"
  by (auto simp add: ae2ce_def lookup_env_restr_eq edom_def a2c_simp)

lemma edom_ae2ce[simp]: "edom (ae2ce ae) = edom ae"
  unfolding edom_def
  by (auto simp add: ae2ce_def  a2c_simp)


definition cHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> (var \<Rightarrow> two)"
  where "cHeap \<Gamma> e = (\<Lambda> a. ae2ce (Aheap \<Gamma> e\<cdot>a))"
lemma cHeap_simp[simp]: "cHeap \<Gamma> e\<cdot>a = ae2ce (Aheap \<Gamma> e\<cdot>a)"
  unfolding cHeap_def by simp

sublocale CardinalityHeap cHeap.

sublocale CardinalityHeapSafe cHeap Aheap
  apply standard
  apply (erule Aheap_thunk)
  apply simp
  done

fun prognosis where 
  "prognosis ae as a (\<Gamma>, e, S) = ((\<lambda>_. many) f|` (edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aexp e\<cdot>a) \<union> edom (AEstack as S)))"

lemma record_all_noop[simp]:
  "record_call x\<cdot>((\<lambda>_. many) f|` S) = (\<lambda>_. many) f|` S"
  by (auto simp add: record_call_def lookup_env_restr_eq)

lemma const_on_restr_constI[intro]:
  "S' \<subseteq> S \<Longrightarrow> const_on ((\<lambda> _. x) f|` S) S' x"
  by fastforce

lemma ap_subset_edom_AEstack: "ap S \<subseteq> edom (AEstack as S)"
  by (induction as S rule:AEstack.induct) (auto simp del: fun_meet_simp)
  

sublocale CardinalityPrognosis prognosis.

sublocale CardinalityPrognosisShape prognosis
proof (standard, goal_cases)
  case 1
  thus ?case by (simp cong: Abinds_env_restr_cong)
next
  case 2
  thus ?case by (simp cong: Abinds_reorder)
next
  case 3
  thus ?case by (auto dest: subsetD[OF ap_subset_edom_AEstack])
next
  case 4
  thus ?case by (auto intro: env_restr_mono2 )
next
  case (5 ae x as a \<Gamma> e S)
  from \<open>ae x = \<bottom>\<close>
  have "ABinds (delete x \<Gamma>)\<cdot>ae = ABinds \<Gamma>\<cdot>ae" by (rule ABinds_delete_bot)
  thus ?case by simp
next
  case (6 ae as a \<Gamma> x S)
  from Aexp_Var[where n = a and x = x]
  have "(Aexp (Var x)\<cdot>a) x \<noteq> \<bottom>" by auto
  hence "x \<in> edom (Aexp (Var x)\<cdot>a)" by (simp add: edomIff)
  thus ?case by simp
qed

sublocale CardinalityPrognosisApp prognosis
proof (standard, goal_cases)
  case 1
  thus ?case
    using edom_mono[OF Aexp_App] by (auto intro!: env_restr_mono2)
qed

sublocale CardinalityPrognosisLam prognosis
proof (standard, goal_cases)
  case (1 ae as a \<Gamma> e y x S)
  have "edom (Aexp e[y::=x]\<cdot>(pred\<cdot>a)) \<subseteq> insert x (edom (env_delete y (Aexp e\<cdot>(pred\<cdot>a))))"
    by (auto dest: subsetD[OF edom_mono[OF Aexp_subst]] )
  also have "\<dots> \<subseteq> insert x (edom (Aexp (Lam [y]. e)\<cdot>a))"
    using edom_mono[OF Aexp_Lam] by auto
  finally show ?case by (auto intro!: env_restr_mono2)
qed

sublocale CardinalityPrognosisVar prognosis
proof (standard, goal_cases)
  case prems: 1
  thus ?case by (auto intro!: env_restr_mono2 simp add: Abinds_reorder1[OF prems(1)])
next
  case prems: 2
  thus ?case
    by (auto intro!: env_restr_mono2 simp add: Abinds_reorder1[OF prems(1)])
       (metis Aexp_Var edomIff not_up_less_UU)
next
  case (3 e x \<Gamma> ae as S)
  have "fup\<cdot>(Aexp e)\<cdot>(ae x) \<sqsubseteq> Aexp e\<cdot>0" by (cases "ae x") (auto intro: monofun_cfun_arg)
  from edom_mono[OF this]
  show ?case by (auto intro!: env_restr_mono2 dest: subsetD[OF edom_mono[OF ABinds_delete_below]])
qed

sublocale CardinalityPrognosisIfThenElse prognosis
proof (standard, goal_cases)
  case (1 ae a as \<Gamma> scrut e1 e2 S)
  have "edom (Aexp scrut\<cdot>0 \<squnion> Aexp e1\<cdot>a \<squnion> Aexp e2\<cdot>a) \<subseteq> edom (Aexp (scrut ? e1 : e2)\<cdot>a)"
    by (rule edom_mono[OF Aexp_IfThenElse])
  thus ?case
    by (auto intro!: env_restr_mono2)
next
  case (2 ae as a \<Gamma> b e1 e2 S)
  show ?case by (auto intro!: env_restr_mono2)
qed

  
sublocale CardinalityPrognosisLet prognosis  cHeap Aheap
proof (standard, goal_cases)
  case prems: (1 \<Delta> \<Gamma> S ae e a as)

  from subsetD[OF prems(3)] fresh_distinct[OF prems(1)] fresh_distinct_fv[OF prems(2)]
  have  "ae f|` domA \<Delta> = \<bottom>"
    by (auto dest: subsetD[OF ups_fv_subset])
  hence [simp]: "ABinds \<Delta>\<cdot>(ae \<squnion> Aheap \<Delta> e\<cdot>a) = ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)" by (simp cong: Abinds_env_restr_cong add: env_restr_join)

  from  fresh_distinct[OF prems(1)]
  have "Aheap \<Delta> e\<cdot>a f|` domA \<Gamma> = \<bottom>" by (auto dest!: subsetD[OF edom_Aheap])
  hence [simp]: "ABinds \<Gamma>\<cdot>(ae \<squnion> Aheap \<Delta> e\<cdot>a) = ABinds \<Gamma>\<cdot>ae" by (simp cong: Abinds_env_restr_cong add: env_restr_join)
  
  have "edom (ABinds (\<Delta> @ \<Gamma>)\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae)) \<union> edom (Aexp e\<cdot>a)  = edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) \<union> edom (ABinds \<Gamma>\<cdot>ae) \<union>  edom (Aexp e\<cdot>a) "
    by (simp add: Abinds_append_disjoint[OF fresh_distinct[OF prems(1)]] Un_commute)
  also have "\<dots> = edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a)"
    by force
  also have "\<dots> \<subseteq> edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a)"
    using  edom_mono[OF Aexp_Let] by force
  also have "\<dots> = edom (Aheap \<Delta> e\<cdot>a) \<union> edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)"
    by auto
  finally
  have "edom (ABinds (\<Delta> @ \<Gamma>)\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae)) \<union> edom (Aexp e\<cdot>a) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a)".
  hence "edom (ABinds (\<Delta> @ \<Gamma>)\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae)) \<union> edom (Aexp e\<cdot>a) \<union> edom (AEstack as S) \<subseteq> edom (Aheap \<Delta> e\<cdot>a) \<union> edom (ABinds \<Gamma>\<cdot>ae) \<union> edom (Aexp (Let \<Delta> e)\<cdot>a) \<union> edom (AEstack as S)" by auto
  thus ?case by (simp add: ae2ce_to_env_restr env_restr_join2 Un_assoc[symmetric] env_restr_mono2)
qed

sublocale CardinalityPrognosisEdom prognosis
  by standard (auto dest: subsetD[OF Aexp_edom] subsetD[OF ap_fv_subset] subsetD[OF edom_AnalBinds]  subsetD[OF edom_AEstack])


sublocale CardinalityPrognosisSafe prognosis cHeap Aheap Aexp..
end

end
