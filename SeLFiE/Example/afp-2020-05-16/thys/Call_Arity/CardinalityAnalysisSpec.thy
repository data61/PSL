theory CardinalityAnalysisSpec
imports ArityAnalysisSpec CardinalityAnalysisSig ConstOn
begin

locale CardinalityPrognosisEdom = CardinalityPrognosis +
  assumes edom_prognosis:
    "edom (prognosis ae as a (\<Gamma>, e, S)) \<subseteq> fv \<Gamma> \<union> fv e \<union> fv S"

locale CardinalityPrognosisShape = CardinalityPrognosis +
  assumes prognosis_env_cong: "ae f|` domA \<Gamma> = ae' f|` domA \<Gamma> \<Longrightarrow> prognosis ae as u (\<Gamma>, e, S) = prognosis ae' as u (\<Gamma>, e, S)"
  assumes prognosis_reorder: "map_of \<Gamma> = map_of \<Delta>  \<Longrightarrow>  prognosis ae as u (\<Gamma>, e, S) = prognosis ae as u (\<Delta>, e, S)"
  assumes prognosis_ap: "const_on (prognosis ae as a (\<Gamma>, e, S)) (ap S) many"
  assumes prognosis_upd: "prognosis ae as u (\<Gamma>, e, S) \<sqsubseteq> prognosis ae as u (\<Gamma>, e, Upd x # S)"
  assumes prognosis_not_called: "ae x = \<bottom> \<Longrightarrow> prognosis ae as a (\<Gamma>, e, S) \<sqsubseteq> prognosis ae as a (delete x \<Gamma>, e, S)"
  assumes prognosis_called: "once \<sqsubseteq> prognosis ae as a (\<Gamma>, Var x, S) x"

locale CardinalityPrognosisApp = CardinalityPrognosis +
  assumes prognosis_App: "prognosis ae as (inc\<cdot>a) (\<Gamma>, e, Arg x # S) \<sqsubseteq> prognosis ae as a (\<Gamma>, App e x, S)"

locale CardinalityPrognosisLam = CardinalityPrognosis +
  assumes prognosis_subst_Lam: "prognosis ae as (pred\<cdot>a) (\<Gamma>, e[y::=x], S) \<sqsubseteq> prognosis ae as a (\<Gamma>, Lam [y]. e, Arg x # S)"

locale CardinalityPrognosisVar = CardinalityPrognosis +
  assumes prognosis_Var_lam: "map_of \<Gamma> x = Some e \<Longrightarrow> ae x = up\<cdot>u \<Longrightarrow> isVal e \<Longrightarrow> prognosis ae as u (\<Gamma>, e, S) \<sqsubseteq> record_call x \<cdot> (prognosis ae as a (\<Gamma>, Var x, S))"
  assumes prognosis_Var_thunk: "map_of \<Gamma> x = Some e \<Longrightarrow> ae x = up\<cdot>u \<Longrightarrow> \<not> isVal e \<Longrightarrow> prognosis ae as u (delete x \<Gamma>, e, Upd x # S) \<sqsubseteq> record_call x \<cdot> (prognosis ae as a (\<Gamma>, Var x, S))"
  assumes prognosis_Var2: "isVal e \<Longrightarrow> x \<notin> domA \<Gamma> \<Longrightarrow> prognosis ae as 0 ((x, e) # \<Gamma>, e, S) \<sqsubseteq> prognosis ae as 0 (\<Gamma>, e, Upd x # S)"

locale CardinalityPrognosisIfThenElse = CardinalityPrognosis +
  assumes prognosis_IfThenElse: "prognosis ae (a#as) 0 (\<Gamma>, scrut, Alts e1 e2 # S) \<sqsubseteq> prognosis ae as a (\<Gamma>, scrut ? e1 : e2, S)"
  assumes prognosis_Alts: "prognosis ae as a (\<Gamma>, if b then e1 else e2, S) \<sqsubseteq> prognosis ae (a#as) 0 (\<Gamma>, Bool b, Alts e1 e2 # S)"

locale CardinalityPrognosisLet = CardinalityPrognosis + CardinalityHeap + ArityAnalysisHeap +
  assumes prognosis_Let:
  "atom ` domA \<Delta> \<sharp>* \<Gamma> \<Longrightarrow> atom ` domA \<Delta> \<sharp>* S \<Longrightarrow> edom ae \<subseteq> domA \<Gamma> \<union> upds S \<Longrightarrow> prognosis (Aheap \<Delta> e\<cdot>a \<squnion> ae) as a (\<Delta> @ \<Gamma>, e, S) \<sqsubseteq> cHeap \<Delta> e\<cdot>a \<squnion> prognosis ae as a (\<Gamma>, Terms.Let \<Delta> e, S)"

locale CardinalityHeapSafe = CardinalityHeap + ArityAnalysisHeap +
  assumes Aheap_heap3: "x \<in> thunks \<Gamma> \<Longrightarrow> many \<sqsubseteq> (cHeap \<Gamma> e\<cdot>a) x \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
  assumes edom_cHeap: "edom (cHeap \<Delta> e\<cdot>a) = edom (Aheap \<Delta> e\<cdot>a)"

locale CardinalityPrognosisSafe =
  CardinalityPrognosisEdom +
  CardinalityPrognosisShape +
  CardinalityPrognosisApp +
  CardinalityPrognosisLam + 
  CardinalityPrognosisVar +
  CardinalityPrognosisLet +
  CardinalityPrognosisIfThenElse +
  CardinalityHeapSafe +
  ArityAnalysisLetSafe

end
