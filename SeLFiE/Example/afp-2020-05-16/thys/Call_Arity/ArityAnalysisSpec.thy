theory ArityAnalysisSpec
imports ArityAnalysisAbinds
begin

locale SubstArityAnalysis = EdomArityAnalysis + 
  assumes Aexp_subst_restr: "x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> (Aexp e[x::=y] \<cdot> a) f|` S = (Aexp e\<cdot>a) f|` S"

locale ArityAnalysisSafe = SubstArityAnalysis +
  assumes Aexp_Var: "up \<cdot> n \<sqsubseteq> (Aexp (Var x)\<cdot>n) x"
  assumes Aexp_App: "Aexp e \<cdot>(inc\<cdot>n) \<squnion> esing x \<cdot> (up\<cdot>0) \<sqsubseteq>  Aexp (App e x) \<cdot> n"
  assumes Aexp_Lam: "env_delete y (Aexp e \<cdot>(pred\<cdot>n)) \<sqsubseteq> Aexp (Lam [y]. e) \<cdot> n"
  assumes Aexp_IfThenElse: "Aexp scrut\<cdot>0 \<squnion> Aexp e1\<cdot>a \<squnion> Aexp e2\<cdot>a \<sqsubseteq> Aexp (scrut ? e1 : e2)\<cdot>a"

locale ArityAnalysisHeapSafe = ArityAnalysisSafe + ArityAnalysisHeapEqvt +
  assumes edom_Aheap: "edom (Aheap \<Gamma> e\<cdot> a) \<subseteq> domA \<Gamma>"
  assumes Aheap_subst: "x \<notin> domA \<Gamma> \<Longrightarrow> y \<notin> domA \<Gamma> \<Longrightarrow> Aheap \<Gamma>[x::h=y] e[x ::=y]  = Aheap \<Gamma> e"

locale ArityAnalysisLetSafe = ArityAnalysisHeapSafe +
  assumes Aexp_Let: "ABinds \<Gamma>\<cdot>(Aheap \<Gamma> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Gamma> e\<cdot>a \<squnion> Aexp (Let \<Gamma> e)\<cdot>a"

locale ArityAnalysisLetSafeNoCard = ArityAnalysisLetSafe +
  assumes Aheap_heap3: "x \<in> thunks \<Gamma> \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"

context SubstArityAnalysis
begin
  lemma Aexp_subst_upd: "(Aexp e[y::=x]\<cdot>n) \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"
  proof-
    have "Aexp e[y::=x]\<cdot>n f|`(-{x,y}) = Aexp e\<cdot>n f|` (-{x,y})" by (rule Aexp_subst_restr) auto
  
    show ?thesis
    proof (rule fun_belowI)
    fix x'
      have "x' = x \<or> x' = y \<or> x' \<in> (-{x,y})" by auto
      thus "(Aexp e[y::=x]\<cdot>n) x' \<sqsubseteq> ((Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)) x'"
      proof(elim disjE)
        assume "x' \<in> (-{x,y})"
        moreover
        have "Aexp e[y::=x]\<cdot>n f|`(-{x,y}) = Aexp e\<cdot>n f|` (-{x,y})" by (rule Aexp_subst_restr) auto
        note fun_cong[OF this, where x = x']
        ultimately
        show ?thesis by auto
      next
        assume "x' = x"
        thus ?thesis by simp
      next
        assume "x' = y"
        thus ?thesis
        using [[simp_trace]]
        by simp
     qed
   qed
  qed

  lemma Aexp_subst: "Aexp (e[y::=x])\<cdot>a \<sqsubseteq> env_delete y ((Aexp e)\<cdot>a) \<squnion> esing x\<cdot>(up\<cdot>0)"
    apply (rule below_trans[OF Aexp_subst_upd])
    apply (rule fun_belowI)
    apply auto
    done
end

context ArityAnalysisSafe
begin

lemma Aexp_Var_singleton: "esing x \<cdot> (up\<cdot>n) \<sqsubseteq> Aexp (Var x) \<cdot> n"
  by (simp add: Aexp_Var)

lemma fup_Aexp_Var: "esing x \<cdot> n \<sqsubseteq> fup\<cdot>(Aexp (Var x))\<cdot>n"
  by (cases n) (simp_all add: Aexp_Var)
end


context ArityAnalysisLetSafe
begin
  lemma Aheap_nonrec:
    assumes "nonrec \<Delta>"
    shows "Aexp e\<cdot>a f|` domA \<Delta> \<sqsubseteq> Aheap \<Delta> e\<cdot>a"
  proof-
    have "ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) \<squnion> Aexp e\<cdot>a \<sqsubseteq> Aheap \<Delta> e\<cdot>a \<squnion> Aexp (Let \<Delta> e)\<cdot>a" by (rule Aexp_Let)
    note env_restr_mono[where S = "domA \<Delta>", OF this]
    moreover
    from assms
    have "ABinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a) f|` domA \<Delta> = \<bottom>"
      by (rule nonrecE) (auto simp add: fv_def fresh_def dest!: subsetD[OF fup_Aexp_edom])
    moreover
    have "Aheap \<Delta> e\<cdot>a f|` domA \<Delta> = Aheap \<Delta> e\<cdot>a" 
      by (rule env_restr_useless[OF edom_Aheap])
    moreover
    have "(Aexp (Let \<Delta> e)\<cdot>a) f|` domA \<Delta> = \<bottom>" 
      by (auto dest!: subsetD[OF Aexp_edom])
    ultimately
    show "Aexp e\<cdot>a f|` domA \<Delta> \<sqsubseteq> Aheap \<Delta> e\<cdot>a"
      by (simp add: env_restr_join)
  qed
end


end
