theory CoCallImplTTree
imports TTreeAnalysisSig "Env-Set-Cpo" CoCallAritySig "CoCallGraph-TTree"
begin

context CoCallArity
begin
  definition Texp :: "exp \<Rightarrow> Arity \<rightarrow> var ttree"
    where "Texp e = (\<Lambda> a. ccTTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a))"
  
  lemma Texp_simp: "Texp e\<cdot>a = ccTTree (edom (Aexp e \<cdot>a)) (ccExp e\<cdot>a)"
    unfolding Texp_def
    by simp

  sublocale TTreeAnalysis Texp.
end



end

