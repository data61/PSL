theory CardinalityAnalysisSig
imports Arity AEnv "Cardinality-Domain" SestoftConf
begin

locale CardinalityPrognosis = 
  fixes prognosis :: "AEnv \<Rightarrow> Arity list \<Rightarrow> Arity \<Rightarrow> conf \<Rightarrow> (var \<Rightarrow> two)"

locale CardinalityHeap = 
  fixes cHeap :: "heap \<Rightarrow> exp \<Rightarrow> Arity \<rightarrow> (var \<Rightarrow> two)"
end
