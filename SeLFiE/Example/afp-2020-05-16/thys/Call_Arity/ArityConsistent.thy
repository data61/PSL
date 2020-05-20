theory ArityConsistent
imports  ArityAnalysisSpec  ArityStack ArityAnalysisStack
begin

context ArityAnalysisLetSafe
begin

type_synonym astate = "(AEnv \<times> Arity \<times> Arity list)"

inductive stack_consistent :: "Arity list \<Rightarrow> stack \<Rightarrow> bool"
  where 
    "stack_consistent [] []"
  | "Astack S \<sqsubseteq> a \<Longrightarrow> stack_consistent as S \<Longrightarrow> stack_consistent (a#as) (Alts e1 e2 # S)"
  | "stack_consistent as S \<Longrightarrow> stack_consistent as (Upd x # S)"
  | "stack_consistent as S \<Longrightarrow> stack_consistent as (Arg x # S)"
inductive_simps stack_consistent_foo[simp]:
  "stack_consistent [] []" "stack_consistent (a#as) (Alts e1 e2 # S)" "stack_consistent as (Upd x # S)" "stack_consistent as (Arg x # S)"
inductive_cases [elim!]: "stack_consistent as (Alts e1 e2 # S)"

inductive a_consistent :: "astate \<Rightarrow> conf \<Rightarrow> bool" where
  a_consistentI:
  "edom ae \<subseteq> domA \<Gamma> \<union> upds S
  \<Longrightarrow> Astack S \<sqsubseteq> a
  \<Longrightarrow> (ABinds \<Gamma>\<cdot>ae \<squnion> Aexp e\<cdot>a \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae
  \<Longrightarrow> stack_consistent as S
  \<Longrightarrow> a_consistent (ae, a, as) (\<Gamma>, e, S)"  
inductive_cases a_consistentE: "a_consistent (ae, a, as) (\<Gamma>, e, S)"

lemma a_consistent_restrictA:
  assumes "a_consistent (ae, a, as) (\<Gamma>, e, S)"
  assumes "edom ae \<subseteq> V"
  shows "a_consistent (ae, a, as) (restrictA V \<Gamma>, e, S)"
proof-
  have "domA \<Gamma> \<inter> V \<union> upds S \<subseteq> domA \<Gamma> \<union> upds S" by auto
  note * = below_trans[OF env_restr_mono2[OF this]]
  
  show " a_consistent (ae, a, as) (restrictA V \<Gamma>, e, S)"
    using assms
    by (auto simp add: a_consistent.simps env_restr_join join_below_iff ABinds_restrict_edom
                  intro: * below_trans[OF env_restr_mono[OF ABinds_restrict_below]])
qed

lemma a_consistent_edom_subsetD:
  "a_consistent (ae, a, as) (\<Gamma>, e, S) \<Longrightarrow> edom ae \<subseteq> domA \<Gamma> \<union> upds S"
  by (rule a_consistentE)

lemma a_consistent_stackD:
  "a_consistent (ae, a, as) (\<Gamma>, e, S) \<Longrightarrow> Astack S \<sqsubseteq> a"
  by (rule a_consistentE)


lemma a_consistent_app\<^sub>1:
  "a_consistent (ae, a, as) (\<Gamma>, App e x, S) \<Longrightarrow> a_consistent (ae, inc\<cdot>a, as) (\<Gamma>, e, Arg x # S)"
  by (auto simp add: join_below_iff env_restr_join a_consistent.simps
           dest!: below_trans[OF env_restr_mono[OF Aexp_App]]
           elim: below_trans)

lemma a_consistent_app\<^sub>2:
  assumes "a_consistent (ae, a, as) (\<Gamma>, (Lam [y]. e), Arg x # S)"
  shows "a_consistent (ae, (pred\<cdot>a), as) (\<Gamma>, e[y::=x], S)"
proof-
  have "Aexp (e[y::=x])\<cdot>(pred\<cdot>a) f|` (domA \<Gamma> \<union> upds S)  \<sqsubseteq> (env_delete y ((Aexp e)\<cdot>(pred\<cdot>a)) \<squnion> esing x\<cdot>(up\<cdot>0)) f|` (domA \<Gamma> \<union> upds S)" by (rule env_restr_mono[OF Aexp_subst])
  also have "\<dots> =  env_delete y ((Aexp e)\<cdot>(pred\<cdot>a)) f|` (domA \<Gamma> \<union> upds S) \<squnion> esing x\<cdot>(up\<cdot>0) f|` (domA \<Gamma> \<union> upds S)" by (simp add: env_restr_join)
  also have "env_delete y ((Aexp e)\<cdot>(pred\<cdot>a)) \<sqsubseteq> Aexp (Lam [y]. e)\<cdot>a" by (rule Aexp_Lam)
  also have "\<dots> f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" using assms  by (auto simp add: join_below_iff env_restr_join a_consistent.simps)
  also have "esing x\<cdot>(up\<cdot>0) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" using assms
    by (cases "x\<in>edom ae") (auto simp add: env_restr_join join_below_iff a_consistent.simps)
  also have "ae \<squnion> ae = ae" by simp
  finally
  have "Aexp (e[y::=x])\<cdot>(pred\<cdot>a) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" by this simp_all
  thus ?thesis using assms
    by (auto elim: below_trans edom_mono  simp add: join_below_iff env_restr_join a_consistent.simps)
qed

lemma a_consistent_thunk_0:
  assumes "a_consistent (ae, a, as) (\<Gamma>, Var x, S)"
  assumes "map_of \<Gamma> x = Some e"
  assumes "ae x = up\<cdot>0"
  shows "a_consistent (ae, 0, as) (delete x \<Gamma>, e, Upd x # S)"
proof-
  from assms(2)
  have [simp]: "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)

  from assms(3)
  have [simp]: "x \<in> edom ae" by (auto simp add: edom_def)

  have "x \<in> domA \<Gamma>" by (metis assms(2) domI dom_map_of_conv_domA)
  hence [simp]: "insert x (domA \<Gamma> - {x} \<union> upds S)  = (domA \<Gamma> \<union> upds S)"
    by auto

  from Abinds_reorder1[OF \<open>map_of \<Gamma> x = Some e\<close>] \<open>ae x = up\<cdot>0\<close>
  have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>0 = ABinds \<Gamma>\<cdot>ae" by (auto intro: join_comm)
  moreover have "(\<dots> \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae"
    using assms(1) by (auto simp add: join_below_iff env_restr_join a_consistent.simps)
  ultimately have "((ABinds (delete x \<Gamma>))\<cdot>ae \<squnion> Aexp e\<cdot>0 \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" by simp
  then
  show ?thesis
     using \<open>ae x = up\<cdot>0\<close> assms(1)
     by (auto simp add: join_below_iff env_restr_join  a_consistent.simps)
qed

lemma a_consistent_thunk_once:
  assumes "a_consistent (ae, a, as) (\<Gamma>, Var x, S)"
  assumes "map_of \<Gamma> x = Some e"
  assumes [simp]: "ae x = up\<cdot>u"
  assumes "heap_upds_ok (\<Gamma>, S)"
  shows "a_consistent (env_delete x ae, u, as) (delete x \<Gamma>, e, S)"
proof-
  from assms(2)
  have [simp]: "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)

  from assms(1) have "Aexp (Var x)\<cdot>a f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" by (auto simp add: join_below_iff env_restr_join a_consistent.simps)
  from fun_belowD[where x = x, OF this] 
  have "(Aexp (Var x)\<cdot>a) x \<sqsubseteq> up\<cdot>u" by simp
  from below_trans[OF Aexp_Var this]
  have "a \<sqsubseteq> u" by simp

  from \<open>heap_upds_ok (\<Gamma>, S)\<close>
  have "x \<notin> upds S" by (auto simp add: a_consistent.simps elim!: heap_upds_okE)
  hence [simp]: "(- {x} \<inter> (domA \<Gamma> \<union> upds S)) = (domA \<Gamma> - {x} \<union> upds S)" by auto

  have "Astack S \<sqsubseteq> u" using assms(1) \<open>a \<sqsubseteq> u\<close>
    by (auto elim: below_trans simp add: a_consistent.simps)
  
  from Abinds_reorder1[OF \<open>map_of \<Gamma> x = Some e\<close>] \<open>ae x = up\<cdot>u\<close>
  have "ABinds (delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u = ABinds \<Gamma>\<cdot>ae" by (auto intro: join_comm)
  moreover
  have "(\<dots> \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae"
    using assms(1) by (auto simp add: join_below_iff env_restr_join a_consistent.simps)
  ultimately
  have "((ABinds (delete x \<Gamma>))\<cdot>ae \<squnion> Aexp e\<cdot>u \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" by simp
  hence "((ABinds (delete x \<Gamma>))\<cdot>(env_delete x ae) \<squnion> Aexp e\<cdot>u \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae"
    by (auto simp add: join_below_iff env_restr_join elim:  below_trans[OF env_restr_mono[OF monofun_cfun_arg[OF env_delete_below_arg]]])
  hence "env_delete x (((ABinds (delete x \<Gamma>))\<cdot>(env_delete x ae) \<squnion> Aexp e\<cdot>u \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S)) \<sqsubseteq> env_delete x ae"
    by (rule env_delete_mono)
  hence "(((ABinds (delete x \<Gamma>))\<cdot>(env_delete x ae) \<squnion> Aexp e\<cdot>u \<squnion> AEstack as S) f|` (domA (delete x \<Gamma>) \<union> upds S)) \<sqsubseteq> env_delete x ae"
    by (simp add: env_delete_restr)
  then
  show ?thesis
     using \<open>ae x = up\<cdot>u\<close> \<open>Astack S \<sqsubseteq> u\<close> assms(1)
     by (auto simp add: join_below_iff env_restr_join  a_consistent.simps elim : below_trans)
qed

lemma a_consistent_lamvar:
  assumes "a_consistent (ae, a, as) (\<Gamma>, Var x, S)"
  assumes "map_of \<Gamma> x = Some e"
  assumes [simp]: "ae x = up\<cdot>u"
  shows "a_consistent (ae, u, as) ((x,e)# delete x \<Gamma>, e, S)"
proof-
  have [simp]: "x \<in> domA \<Gamma>" by (metis assms(2) domI dom_map_of_conv_domA)
  have [simp]: "insert x (domA \<Gamma> \<union> upds S) = (domA \<Gamma> \<union> upds S)" 
    by auto

  from assms(1) have "Aexp (Var x)\<cdot>a f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" by (auto simp add: join_below_iff env_restr_join a_consistent.simps)
  from fun_belowD[where x = x, OF this] 
  have "(Aexp (Var x)\<cdot>a) x \<sqsubseteq> up\<cdot>u" by simp
  from below_trans[OF Aexp_Var this]
  have "a \<sqsubseteq> u" by simp

  have "Astack S \<sqsubseteq> u" using assms(1) \<open>a \<sqsubseteq> u\<close>
    by (auto elim: below_trans simp add: a_consistent.simps)
  
  from Abinds_reorder1[OF \<open>map_of \<Gamma> x = Some e\<close>] \<open>ae x = up\<cdot>u\<close>
  have "ABinds ((x,e) # delete x \<Gamma>)\<cdot>ae \<squnion> Aexp e\<cdot>u = ABinds \<Gamma>\<cdot>ae" by (auto intro: join_comm)
  moreover
  have "(\<dots> \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae"
    using assms(1) by (auto simp add: join_below_iff env_restr_join a_consistent.simps)
  ultimately
  have "((ABinds ((x,e) # delete x \<Gamma>))\<cdot>ae \<squnion> Aexp e\<cdot>u \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" by simp
  then
  show ?thesis
     using \<open>ae x = up\<cdot>u\<close> \<open>Astack S \<sqsubseteq> u\<close> assms(1)
     by (auto simp add: join_below_iff env_restr_join  a_consistent.simps)
qed

lemma 
  assumes "a_consistent (ae, a, as) (\<Gamma>, e, Upd x # S)"
  shows a_consistent_var\<^sub>2: "a_consistent (ae, a, as) ((x, e) # \<Gamma>, e, S)" 
    and a_consistent_UpdD: "ae x = up\<cdot>0""a = 0"
    using assms
    by (auto simp add: join_below_iff env_restr_join a_consistent.simps 
               elim:below_trans[OF env_restr_mono[OF ABinds_delete_below]])

lemma a_consistent_let:
  assumes "a_consistent (ae, a, as) (\<Gamma>, Let \<Delta> e, S)"
  assumes "atom ` domA \<Delta> \<sharp>* \<Gamma>"
  assumes "atom ` domA \<Delta> \<sharp>* S"
  assumes "edom ae \<inter> domA \<Delta> = {}"
  shows "a_consistent (Aheap \<Delta> e\<cdot>a \<squnion> ae, a, as) (\<Delta> @ \<Gamma>, e, S)"
proof-
  txt \<open>
    First some boring stuff about scope:
\<close>
  
  have [simp]: "\<And> S. S \<subseteq> domA \<Delta> \<Longrightarrow> ae f|` S = \<bottom>" using assms(4) by auto
  have [simp]: "ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae) = ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)"
    by (rule Abinds_env_restr_cong) (simp add: env_restr_join)

  have [simp]: "Aheap \<Delta> e\<cdot>a f|` domA \<Gamma> = \<bottom>"
    using fresh_distinct[OF assms(2)]
    by (auto intro: env_restr_empty dest!: subsetD[OF edom_Aheap])

  have [simp]: "ABinds \<Gamma>\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae) = ABinds \<Gamma>\<cdot>ae"
    by (rule Abinds_env_restr_cong) (simp add: env_restr_join)

  have [simp]: "ABinds \<Gamma>\<cdot>ae f|` (domA \<Delta> \<union> domA \<Gamma> \<union> upds S)  = ABinds \<Gamma>\<cdot>ae f|` (domA \<Gamma> \<union> upds S)" 
    using fresh_distinct_fv[OF assms(2)]
    by (auto intro: env_restr_cong dest!: subsetD[OF edom_AnalBinds])

  have [simp]: "AEstack as S f|` (domA \<Delta> \<union> domA \<Gamma> \<union> upds S) = AEstack as S f|` (domA \<Gamma> \<union> upds S)" 
    using fresh_distinct_fv[OF assms(3)]
    by (auto intro: env_restr_cong dest!:  subsetD[OF edom_AEstack])

  have [simp]: "Aexp (Let \<Delta> e)\<cdot>a f|` (domA \<Delta> \<union> domA \<Gamma> \<union> upds S) = Aexp (Terms.Let \<Delta> e)\<cdot>a f|` (domA \<Gamma> \<union> upds S)"
    by (rule env_restr_cong) (auto dest!: subsetD[OF Aexp_edom])
  
  have [simp]: "Aheap \<Delta> e\<cdot>a f|` (domA \<Delta> \<union> domA \<Gamma> \<union> upds S) = Aheap \<Delta> e\<cdot>a "
    by (rule env_restr_useless) (auto dest!: subsetD[OF edom_Aheap])

  have "((ABinds \<Gamma>)\<cdot>ae \<squnion> AEstack as S) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" using assms(1) by (auto simp add: a_consistent.simps join_below_iff env_restr_join)
  moreover
  have" Aexp (Let \<Delta> e)\<cdot>a f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae"  using assms(1) by (auto simp add: a_consistent.simps join_below_iff env_restr_join)
  moreover
  have "ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a" by (rule Aexp_Let)
  ultimately
  have "(ABinds (\<Delta> @ \<Gamma>)\<cdot>(Aheap \<Delta> e\<cdot>a \<squnion> ae) \<squnion> Aexp e\<cdot>a \<squnion> AEstack as S) f|` (domA (\<Delta>@\<Gamma>) \<union> upds S) \<sqsubseteq> Aheap \<Delta> e\<cdot>a \<squnion> ae"
    by (auto 4 4 simp add: env_restr_join Abinds_append_disjoint[OF fresh_distinct[OF assms(2)]] join_below_iff
                 simp del: join_comm
                 elim: below_trans below_trans[OF env_restr_mono])
  moreover
  note fresh_distinct[OF assms(2)]
  moreover
  from fresh_distinct_fv[OF assms(3)]
  have  "domA \<Delta> \<inter> upds S = {}" by (auto dest!: subsetD[OF ups_fv_subset])
  ultimately
  show ?thesis using assms(1)
    by (auto simp add: a_consistent.simps dest!: subsetD[OF edom_Aheap] intro: heap_upds_ok_append)
qed

lemma a_consistent_if\<^sub>1:
  assumes "a_consistent (ae, a, as) (\<Gamma>, scrut ? e1 : e2, S)"
  shows "a_consistent (ae, 0, a#as) (\<Gamma>, scrut, Alts e1 e2 # S)"
proof-
  from assms
  have "Aexp (scrut ? e1 : e2)\<cdot>a f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" by (auto simp add: a_consistent.simps env_restr_join join_below_iff)
  hence "(Aexp scrut\<cdot>0 \<squnion> Aexp e1\<cdot>a \<squnion> Aexp e2\<cdot>a) f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae"
    by (rule below_trans[OF env_restr_mono[OF Aexp_IfThenElse]])
  thus ?thesis
    using assms
    by (auto simp add: a_consistent.simps join_below_iff env_restr_join)
qed

lemma a_consistent_if\<^sub>2:
  assumes "a_consistent (ae, a, a'#as') (\<Gamma>, Bool b, Alts e1 e2 # S)"
  shows "a_consistent (ae, a', as') (\<Gamma>, if b then e1 else e2, S)"
using assms by (auto simp add: a_consistent.simps join_below_iff env_restr_join)

lemma a_consistent_alts_on_stack:
  assumes "a_consistent (ae, a, as) (\<Gamma>, Bool b, Alts e1 e2 # S)"
  obtains a' as' where "as = a' # as'" "a = 0"
using assms by (auto simp add: a_consistent.simps)

lemma closed_a_consistent:
  "fv e = ({}::var set) \<Longrightarrow> a_consistent (\<bottom>, 0, []) ([], e, [])"
  by (auto simp add: edom_empty_iff_bot a_consistent.simps  dest!: subsetD[OF Aexp_edom])

end

end
