theory Univ imports "~~/src/HOL/BNF/Countable_Type"
begin

(* A fixed countable universe for interpreting countable models  *)

datatype univ = UU nat

lemma infinite_univ[simp]: "infinite (UNIV :: univ set)"
unfolding infinite_iff_card_of_nat card_of_ordLeq[symmetric]
unfolding inj_on_def by auto

lemma countable_univ[simp]: "countable (UNIV :: univ set)"
unfolding countable_card_of_nat apply(rule surj_imp_ordLeq[of _ UU])
by (metis subset_UNIV surj_def univ.exhaust)


end