theory ArityAnalysisFixProps
imports ArityAnalysisFix ArityAnalysisSpec
begin

context SubstArityAnalysis
begin

lemma Afix_restr_subst:
  assumes "x \<notin> S"
  assumes "y \<notin> S"
  assumes "domA \<Gamma> \<subseteq> S"
  shows "Afix \<Gamma>[x::h=y]\<cdot>ae f|` S = Afix \<Gamma>\<cdot>(ae f|` S) f|` S"
  by (rule Afix_restr_subst'[OF Aexp_subst_restr[OF assms(1,2)] assms])
end


end
