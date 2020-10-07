theory TrivialArityAnal
imports ArityAnalysisSpec "Launchbury.Env-Nominal"
begin

definition Trivial_Aexp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"
  where "Trivial_Aexp e = (\<Lambda> n. (\<lambda> x. up\<cdot>0) f|` fv e)"

lemma Trivial_Aexp_simp: "Trivial_Aexp e \<cdot> n = (\<lambda> x. up\<cdot>0) f|` fv e"
  unfolding Trivial_Aexp_def by simp

lemma edom_Trivial_Aexp[simp]: "edom (Trivial_Aexp e \<cdot> n) = fv e"
  by (auto simp add: edom_def env_restr_def Trivial_Aexp_def) 

lemma Trivial_Aexp_eq[iff]: "Trivial_Aexp e \<cdot> n = Trivial_Aexp e' \<cdot> n' \<longleftrightarrow> fv e = (fv e' :: var set)"
  apply (auto simp add: Trivial_Aexp_simp env_restr_def)
  apply (metis up_defined)+
  done
  
lemma below_Trivial_Aexp[simp]: "(ae \<sqsubseteq> Trivial_Aexp e \<cdot> n) \<longleftrightarrow> edom ae \<subseteq> fv e"
  by (auto dest:fun_belowD intro!: fun_belowI  simp add: Trivial_Aexp_def env_restr_def edom_def split:if_splits)


interpretation ArityAnalysis Trivial_Aexp.
interpretation EdomArityAnalysis Trivial_Aexp
  by standard simp


interpretation ArityAnalysisSafe Trivial_Aexp
proof
(*
  fix \<pi>
  show "\<pi> \<bullet> Trivial_Aexp = Trivial_Aexp" by perm_simp rule
next
*)
  fix n x
  show "up\<cdot>n \<sqsubseteq> (Trivial_Aexp (Var x)\<cdot>n) x"
    by (simp add: Trivial_Aexp_simp)
next
  fix e x n
  show "Trivial_Aexp e\<cdot>(inc\<cdot>n) \<squnion> esing x\<cdot>(up\<cdot>0) \<sqsubseteq> Trivial_Aexp (App e x)\<cdot>n"
    by (auto intro: fun_belowI simp add: Trivial_Aexp_def env_restr_def )
next
  fix y e n
  show "env_delete y (Trivial_Aexp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> Trivial_Aexp (Lam [y]. e)\<cdot>n"
    by (auto simp add: Trivial_Aexp_simp env_delete_restr Diff_eq inf_commute)
next
  fix x y :: var and S e a
  assume "x \<notin> S" and "y \<notin> S"
  thus "Trivial_Aexp e[x::=y]\<cdot>a f|` S = Trivial_Aexp e\<cdot>a f|` S"
    by (auto simp add: Trivial_Aexp_simp fv_subst_eq intro!: arg_cong[where f = "\<lambda> S. env_restr S e" for e])
next
  fix scrut e1 a e2
  show "Trivial_Aexp scrut\<cdot>0 \<squnion> Trivial_Aexp e1\<cdot>a \<squnion> Trivial_Aexp e2\<cdot>a \<sqsubseteq> Trivial_Aexp (scrut ? e1 : e2)\<cdot>a"
    by (auto intro: env_restr_mono2 simp add: Trivial_Aexp_simp join_below_iff )
qed

definition Trivial_Aheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> AEnv" where
  "Trivial_Aheap \<Gamma> e = (\<Lambda> a. (\<lambda> x. up\<cdot>0) f|` domA \<Gamma>)"

lemma Trivial_Aheap_eqvt[eqvt]: "\<pi> \<bullet>  (Trivial_Aheap \<Gamma> e) = Trivial_Aheap (\<pi> \<bullet> \<Gamma>) (\<pi> \<bullet> e)"
  unfolding Trivial_Aheap_def
  apply perm_simp
  apply (simp add: Abs_cfun_eqvt)
  done

lemma Trivial_Aheap_simp: "Trivial_Aheap \<Gamma> e\<cdot> a = (\<lambda> x. up\<cdot>0) f|` domA \<Gamma>"
  unfolding Trivial_Aheap_def by simp

lemma Trivial_fup_Aexp_below_fv: "fup\<cdot>(Trivial_Aexp e)\<cdot>a \<sqsubseteq> (\<lambda> x . up\<cdot>0) f|` fv e"
  by (cases a)(auto simp add: Trivial_Aexp_simp)

lemma Trivial_Abinds_below_fv: "ABinds \<Gamma>\<cdot>ae \<sqsubseteq> (\<lambda> x . up\<cdot>0) f|` fv \<Gamma>"
  by (induction \<Gamma> rule:ABinds.induct)
     (auto simp add: join_below_iff intro!: below_trans[OF Trivial_fup_Aexp_below_fv] env_restr_mono2 elim: below_trans dest: subsetD[OF fv_delete_subset] simp del: fun_meet_simp)

interpretation ArityAnalysisLetSafe Trivial_Aexp Trivial_Aheap
proof
  fix \<pi>
  show "\<pi> \<bullet> Trivial_Aheap = Trivial_Aheap" by perm_simp rule  
next
  fix \<Gamma> e ae show "edom (Trivial_Aheap \<Gamma> e\<cdot>ae) \<subseteq> domA \<Gamma>"
  by (simp add: Trivial_Aheap_simp)
next
  fix \<Gamma> :: heap and e and a
  show "ABinds \<Gamma>\<cdot>(Trivial_Aheap \<Gamma> e\<cdot>a) \<squnion> Trivial_Aexp e\<cdot>a \<sqsubseteq> Trivial_Aheap \<Gamma> e\<cdot>a \<squnion> Trivial_Aexp (Terms.Let \<Gamma> e)\<cdot>a"
    by (auto simp add: Trivial_Aheap_simp Trivial_Aexp_simp join_below_iff env_restr_join2 intro!: env_restr_mono2 below_trans[OF Trivial_Abinds_below_fv])
next
  fix x y :: var and \<Gamma> :: heap and e
  assume "x \<notin> domA \<Gamma>" and "y \<notin> domA \<Gamma>"
  thus "Trivial_Aheap \<Gamma>[x::h=y] e[x::=y] = Trivial_Aheap \<Gamma> e"
    by (auto intro: cfun_eqI simp add: Trivial_Aheap_simp)
qed

end

