theory ArityAnalysisStack
imports SestoftConf ArityAnalysisSig
begin

context ArityAnalysis
begin
  fun AEstack :: "Arity list \<Rightarrow> stack \<Rightarrow> AEnv"
    where 
      "AEstack _ [] = \<bottom>"
    | "AEstack (a#as) (Alts e1 e2 # S) = Aexp e1\<cdot>a \<squnion> Aexp e2\<cdot>a \<squnion> AEstack as S"
    | "AEstack as (Upd x # S) = esing x\<cdot>(up\<cdot>0) \<squnion> AEstack as S"
    | "AEstack as (Arg x # S) = esing x\<cdot>(up\<cdot>0) \<squnion> AEstack as S"
    | "AEstack as (_ # S) = AEstack as S"
end

context EdomArityAnalysis
begin
  lemma edom_AEstack: "edom (AEstack as S) \<subseteq> fv S"
    by (induction as S rule: AEstack.induct) (auto simp del: fun_meet_simp dest!: subsetD[OF Aexp_edom])
end

end
