(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Code lemmas for abstract definitions\<close>

theory Code_Equations
imports
  LTL Equivalence_Relations
  Boolean_Expression_Checkers.Boolean_Expression_Checkers
  Boolean_Expression_Checkers.Boolean_Expression_Checkers_AList_Mapping
begin

subsection \<open>Propositional Equivalence\<close>

fun ifex_of_ltl :: "'a ltln \<Rightarrow> 'a ltln ifex"
where
  "ifex_of_ltl true\<^sub>n = Trueif"
| "ifex_of_ltl false\<^sub>n = Falseif"
| "ifex_of_ltl (\<phi> and\<^sub>n \<psi>) = normif Mapping.empty (ifex_of_ltl \<phi>) (ifex_of_ltl \<psi>) Falseif"
| "ifex_of_ltl (\<phi> or\<^sub>n \<psi>) = normif Mapping.empty (ifex_of_ltl \<phi>) Trueif (ifex_of_ltl \<psi>)"
| "ifex_of_ltl \<phi> = IF \<phi> Trueif Falseif"

lemma val_ifex:
  "val_ifex (ifex_of_ltl b) s = {x. s x} \<Turnstile>\<^sub>P b"
  by (induction b) (simp add: agree_Nil val_normif)+

lemma reduced_ifex:
  "reduced (ifex_of_ltl b) {}"
  by (induction b) (simp; metis keys_empty reduced_normif)+

lemma ifex_of_ltl_reduced_bdt_checker:
  "reduced_bdt_checkers ifex_of_ltl (\<lambda>y s. {x. s x} \<Turnstile>\<^sub>P y)"
  unfolding reduced_bdt_checkers_def
  using val_ifex reduced_ifex by blast

lemma ltl_prop_equiv_impl[code]:
  "(\<phi> \<sim>\<^sub>P \<psi>) = equiv_test ifex_of_ltl \<phi> \<psi>"
  by (simp add: ltl_prop_equiv_def reduced_bdt_checkers.equiv_test[OF ifex_of_ltl_reduced_bdt_checker]; fastforce)

lemma ltl_prop_implies_impl[code]:
  "(\<phi> \<longrightarrow>\<^sub>P \<psi>) = impl_test ifex_of_ltl \<phi> \<psi>"
  by (simp add: ltl_prop_implies_def reduced_bdt_checkers.impl_test[OF ifex_of_ltl_reduced_bdt_checker]; force)

\<comment> \<open>Check code export\<close>
export_code "(\<sim>\<^sub>P)" "(\<longrightarrow>\<^sub>P)" checking

end
