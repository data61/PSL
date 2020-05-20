theory CoCallAnalysisSig
imports Launchbury.Terms Arity CoCallGraph
begin

locale CoCallAnalysis =
  fixes ccExp :: "exp \<Rightarrow> Arity \<rightarrow> CoCalls"
begin
  abbreviation ccExp_syn ("\<G>\<^bsub>_\<^esub>")
    where "\<G>\<^bsub>a\<^esub> \<equiv> (\<lambda>e. ccExp e\<cdot>a)"
  abbreviation ccExp_bot_syn ("\<G>\<^sup>\<bottom>\<^bsub>_\<^esub>")
    where "\<G>\<^sup>\<bottom>\<^bsub>a\<^esub> \<equiv> (\<lambda>e. fup\<cdot>(ccExp e)\<cdot>a)"
end

locale CoCallAnalyisHeap = 
  fixes ccHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> CoCalls"

end
