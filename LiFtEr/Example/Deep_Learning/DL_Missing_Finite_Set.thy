(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Missing Lemmas of Finite\_Set\<close>
theory DL_Missing_Finite_Set
imports Main
begin

lemma card_even[simp]: "card {a \<in> Collect even. a < 2 * n} = n"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "{a \<in> Collect even. a < 2 * Suc n} = insert (2*n) {a \<in> Collect even. a < 2 * n}"
    using le_eq_less_or_eq less_Suc_eq_le subset_antisym by force
  show ?case
    unfolding `{a \<in> Collect even. a < 2 * Suc n} = insert (2*n) {a \<in> Collect even. a < 2 * n}`
    using Suc card_insert_disjoint[of "{a \<in> Collect even. a < 2 * n}" "2*n"]
    by (simp add: finite_M_bounded_by_nat less_not_refl2)
qed

lemma card_odd[simp]: "card {a \<in> Collect odd. a < 2 * n} = n"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "{a \<in> Collect odd. a < 2 * Suc n} = insert (2*n+1) {a \<in> Collect odd. a < 2 * n}"
    using le_eq_less_or_eq less_Suc_eq_le subset_antisym by force
  show ?case
    unfolding `{a \<in> Collect odd. a < 2 * Suc n} = insert (2*n+1) {a \<in> Collect odd. a < 2 * n}`
    using Suc card_insert_disjoint[of "{a \<in> Collect even. a < 2 * n}" "2*n"]
    by (simp add: finite_M_bounded_by_nat less_not_refl2)
qed

end
