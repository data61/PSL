theory TTreeImplCardinality
imports TTreeAnalysisSig CardinalityAnalysisSig "Cardinality-Domain-Lists"
begin

context TTreeAnalysis
begin

fun unstack :: "stack \<Rightarrow> exp \<Rightarrow> exp" where
  "unstack [] e = e"
| "unstack (Alts e1 e2 # S) e = unstack S e"
| "unstack (Upd x # S) e = unstack S e"
| "unstack (Arg x # S) e = unstack S (App e x)"
| "unstack (Dummy x # S) e = unstack S e"

fun Fstack :: "Arity list \<Rightarrow> stack \<Rightarrow> var ttree"
  where "Fstack _ [] = \<bottom>"
  | "Fstack (a#as) (Alts e1 e2 # S) = (Texp e1\<cdot>a \<oplus>\<oplus> Texp e2\<cdot>a) \<otimes>\<otimes> Fstack as S"
  | "Fstack as (Arg x # S) = many_calls x \<otimes>\<otimes> Fstack as S"
  | "Fstack as (_ # S) = Fstack as S"



(*
lemma carrier_Fstack[simp]: "carrier (Fstack S) = ap S"
  by (induction S rule: Fstack.induct) (auto simp add: empty_is_bottom[symmetric])
*)

fun prognosis :: "AEnv \<Rightarrow> Arity list \<Rightarrow> Arity \<Rightarrow> conf \<Rightarrow> var \<Rightarrow> two"
   where "prognosis ae as a (\<Gamma>, e, S) = pathsCard (paths (substitute (FBinds \<Gamma>\<cdot>ae) (thunks \<Gamma>) (Texp e\<cdot>a \<otimes>\<otimes> Fstack as S)))"
end

end
