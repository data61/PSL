theory TTreeAnalysisSig
imports Arity  "TTree-HOLCF"  AnalBinds
begin

locale TTreeAnalysis =
 fixes Texp :: "exp \<Rightarrow> Arity \<rightarrow> var ttree"
begin
  sublocale Texp: ExpAnalysis Texp.
  abbreviation "FBinds == Texp.AnalBinds"
end

end
