theory TTreeAnalysisSpec
imports TTreeAnalysisSig ArityAnalysisSpec "Cardinality-Domain-Lists"
begin

locale TTreeAnalysisCarrier = TTreeAnalysis + EdomArityAnalysis +
  assumes carrier_Fexp: "carrier (Texp e\<cdot>a) = edom (Aexp e\<cdot>a)"

locale TTreeAnalysisSafe = TTreeAnalysisCarrier +
  assumes Texp_App: "many_calls x \<otimes>\<otimes> (Texp e)\<cdot>(inc\<cdot>a) \<sqsubseteq> Texp (App e x)\<cdot>a"
  assumes Texp_Lam: "without y (Texp e\<cdot>(pred\<cdot>n)) \<sqsubseteq> Texp (Lam [y]. e) \<cdot> n"
  assumes Texp_subst: "Texp (e[y::=x])\<cdot>a \<sqsubseteq> many_calls x \<otimes>\<otimes> without y ((Texp e)\<cdot>a)"
  assumes Texp_Var: "single v \<sqsubseteq> Texp (Var v)\<cdot>a"
  assumes Fun_repeatable: "isVal e \<Longrightarrow> repeatable (Texp e\<cdot>0)"
  assumes Texp_IfThenElse: "Texp scrut\<cdot>0 \<otimes>\<otimes> (Texp e1\<cdot>a \<oplus>\<oplus> Texp e2\<cdot>a) \<sqsubseteq> Texp (scrut ? e1 : e2)\<cdot>a"

locale TTreeAnalysisCardinalityHeap = 
  TTreeAnalysisSafe + ArityAnalysisLetSafe + 
  fixes Theap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> var ttree"
  assumes carrier_Fheap: "carrier (Theap \<Gamma> e\<cdot>a) = edom (Aheap \<Gamma> e\<cdot>a)"
  assumes Theap_thunk: "x \<in> thunks \<Gamma> \<Longrightarrow> p \<in> paths (Theap \<Gamma> e\<cdot>a) \<Longrightarrow> \<not> one_call_in_path x p \<Longrightarrow> (Aheap \<Gamma> e\<cdot>a) x = up\<cdot>0"
  assumes Theap_substitute: "ttree_restr (domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a)) (thunks \<Delta>) (Texp e\<cdot>a)) \<sqsubseteq> Theap \<Delta> e\<cdot>a"
  assumes Texp_Let: "ttree_restr (- domA \<Delta>) (substitute (FBinds \<Delta>\<cdot>(Aheap \<Delta> e\<cdot>a))  (thunks \<Delta>) (Texp e\<cdot>a)) \<sqsubseteq> Texp (Terms.Let \<Delta> e)\<cdot>a"


end
