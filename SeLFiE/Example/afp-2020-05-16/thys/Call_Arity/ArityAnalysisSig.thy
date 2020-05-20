theory ArityAnalysisSig
imports Launchbury.Terms AEnv "Arity-Nominal" "Launchbury.Nominal-HOLCF"  Launchbury.Substitution
begin

locale ArityAnalysis =
  fixes Aexp :: "exp \<Rightarrow> Arity \<rightarrow> AEnv"
begin
  abbreviation Aexp_syn ("\<A>\<^bsub>_\<^esub>")where "\<A>\<^bsub>a\<^esub> e \<equiv> Aexp e\<cdot>a"
  abbreviation Aexp_bot_syn ("\<A>\<^sup>\<bottom>\<^bsub>_\<^esub>")
    where "\<A>\<^sup>\<bottom>\<^bsub>a\<^esub> e \<equiv> fup\<cdot>(Aexp e)\<cdot>a"

end

locale ArityAnalysisHeap =
  fixes Aheap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> AEnv"

locale EdomArityAnalysis = ArityAnalysis + 
  assumes Aexp_edom: "edom (\<A>\<^bsub>a\<^esub> e) \<subseteq> fv e"
begin

  lemma fup_Aexp_edom: "edom (\<A>\<^sup>\<bottom>\<^bsub>a\<^esub> e) \<subseteq> fv e"
    by (cases a) (auto dest:subsetD[OF Aexp_edom])
  
  lemma Aexp_fresh_bot[simp]: assumes "atom v \<sharp> e" shows "\<A>\<^bsub>a\<^esub> e v = \<bottom>"
  proof-
    from assms have "v \<notin> fv e" by (metis fv_not_fresh)
    with Aexp_edom have "v \<notin> edom (\<A>\<^bsub>a\<^esub> e)" by auto
    thus ?thesis unfolding edom_def by simp
  qed
end

locale ArityAnalysisHeapEqvt = ArityAnalysisHeap + 
  assumes Aheap_eqvt[eqvt]: "\<pi> \<bullet> Aheap = Aheap"

end
