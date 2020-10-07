subsubsection\<open>Going back: CNFs to formulas\<close>
theory CNF_To_Formula
imports CNF_Formulas "HOL-Library.List_Lexorder"
begin
  
text\<open>One downside of CNFs is that they cannot be converted back to formulas 
as-is in full generality.
If we assume an order on the atoms, we can convert finite CNFs.\<close>
(* This theory was written after the theories that use the CNF, so I don't really know,
   but I suspect that you won't gain much from using this for the LSC lemmas\<dots> *)

instantiation literal :: (ord) ord
begin

definition
  literal_less_def: "xs < ys \<longleftrightarrow> (
    if atoms_of_lit xs = atoms_of_lit ys
    then (case xs of Neg _ \<Rightarrow> (case ys of Pos _ \<Rightarrow> True | _ \<Rightarrow> False) | _ \<Rightarrow> False)
    else atoms_of_lit xs < atoms_of_lit ys)"
  (* the how doesn't /really/ matter, but I still wanted something somewhat pretty. *)

definition
  literal_le_def: "(xs :: _ literal) \<le> ys \<longleftrightarrow> xs < ys \<or> xs = ys"

instance ..

end

instance literal :: (linorder) linorder
by standard (auto simp add: literal_less_def literal_le_def split: literal.splits if_splits)

definition formula_of_cnf where
  "formula_of_cnf S \<equiv> form_of_cnf (sorted_list_of_set (sorted_list_of_set ` S))"
text\<open>To use the lexicographic order on lists, we first have to convert the clauses to lists,
then the set of lists of literals to a list.\<close>

lemma "simplify_consts (formula_of_cnf ({{Pos 0}} :: nat clause set)) = Atom 0" by code_simp

lemma cnf_formula_of_cnf:
  assumes "finite S" "\<forall>C \<in> S. finite C"
  shows "cnf (formula_of_cnf S) = S"
  using assms by(simp add: cnf_BigAnd formula_of_cnf_def form_of_cnf_def cnf_disj)
(* again, formula_of_cnf \<circ> cnf is not an identity transformation, not even if the formula is_cnf.
   (there may be a much stricter definition of is_cnf for which that is the case) *)
  
end
