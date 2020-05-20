(*
    Author:   Salomon Sickert
    License:  BSD
*)

section \<open>Additional Equivalence Relations\<close>

theory Extra_Equivalence_Relations
imports
  LTL.LTL LTL.Equivalence_Relations After Advice
begin

subsection \<open>Propositional Equivalence with Implicit LTL Unfolding\<close>

fun Unf :: "'a ltln \<Rightarrow> 'a ltln"
where
  "Unf (\<phi> U\<^sub>n \<psi>) = ((\<phi> U\<^sub>n \<psi>) and\<^sub>n Unf \<phi>) or\<^sub>n Unf \<psi>"
| "Unf (\<phi> W\<^sub>n \<psi>) = ((\<phi> W\<^sub>n \<psi>) and\<^sub>n Unf \<phi>) or\<^sub>n Unf \<psi>"
| "Unf (\<phi> M\<^sub>n \<psi>) = ((\<phi> M\<^sub>n \<psi>) or\<^sub>n Unf \<phi>) and\<^sub>n Unf \<psi>"
| "Unf (\<phi> R\<^sub>n \<psi>) = ((\<phi> R\<^sub>n \<psi>) or\<^sub>n Unf \<phi>) and\<^sub>n Unf \<psi>"
| "Unf (\<phi> and\<^sub>n \<psi>) = Unf \<phi> and\<^sub>n Unf \<psi>"
| "Unf (\<phi> or\<^sub>n \<psi>) = Unf \<phi> or\<^sub>n Unf \<psi>"
| "Unf \<phi> = \<phi>"

lemma Unf_sound:
  "w \<Turnstile>\<^sub>n Unf \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof (induction \<phi> arbitrary: w)
  case (Until_ltln \<phi>1 \<phi>2)
  then show ?case
    by (simp, metis less_linear not_less0 suffix_0)
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    by (simp, metis less_linear not_less0 suffix_0)
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
    by (simp, metis bot.extremum_unique bot_nat_def less_eq_nat.simps(1) suffix_0)
qed (simp_all, fastforce)

lemma Unf_lang_equiv:
  "\<phi> \<sim>\<^sub>L Unf \<phi>"
  by (simp add: Unf_sound ltl_lang_equiv_def)

lemma Unf_idem:
  "Unf (Unf \<phi>) \<sim>\<^sub>P Unf \<phi>"
  by (induction \<phi>) (auto simp: ltl_prop_equiv_def)

definition ltl_prop_unfold_equiv :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool" (infix "\<sim>\<^sub>Q" 75)
where
  "\<phi> \<sim>\<^sub>Q \<psi> \<equiv> (Unf \<phi>) \<sim>\<^sub>P (Unf \<psi>)"

lemma ltl_prop_unfold_equiv_equivp:
  "equivp (\<sim>\<^sub>Q)"
  by (metis ltl_prop_equiv_equivp ltl_prop_unfold_equiv_def equivpI equivp_def reflpI sympI transpI)

lemma unfolding_prop_unfold_idem:
  "Unf \<phi> \<sim>\<^sub>Q \<phi>"
  unfolding ltl_prop_unfold_equiv_def by (rule Unf_idem)

lemma unfolding_is_subst: "Unf \<phi> = subst \<phi> (\<lambda>\<psi>. Some (Unf \<psi>))"
  by (induction \<phi>) auto

lemma ltl_prop_equiv_implies_ltl_prop_unfold_equiv:
  "\<phi> \<sim>\<^sub>P \<psi> \<Longrightarrow> \<phi> \<sim>\<^sub>Q \<psi>"
  by (metis ltl_prop_unfold_equiv_def unfolding_is_subst subst_respects_ltl_prop_entailment(2))

lemma ltl_prop_unfold_equiv_implies_ltl_lang_equiv:
  "\<phi> \<sim>\<^sub>Q \<psi> \<Longrightarrow> \<phi> \<sim>\<^sub>L \<psi>"
  by (metis ltl_prop_equiv_implies_ltl_lang_equiv ltl_lang_equiv_def Unf_sound ltl_prop_unfold_equiv_def)

lemma ltl_prop_unfold_equiv_gt_and_lt:
  "(\<sim>\<^sub>C) \<le> (\<sim>\<^sub>Q)" "(\<sim>\<^sub>P) \<le> (\<sim>\<^sub>Q)" "(\<sim>\<^sub>Q) \<le> (\<sim>\<^sub>L)"
  using ltl_prop_equiv_implies_ltl_prop_unfold_equiv ltl_prop_equivalence.ge_const_equiv ltl_prop_unfold_equiv_implies_ltl_lang_equiv
  by blast+

quotient_type 'a ltln\<^sub>Q = "'a ltln" / "(\<sim>\<^sub>Q)"
  by (rule ltl_prop_unfold_equiv_equivp)

instantiation ltln\<^sub>Q :: (type) equal
begin

lift_definition ltln\<^sub>Q_eq_test :: "'a ltln\<^sub>Q \<Rightarrow> 'a ltln\<^sub>Q \<Rightarrow> bool" is "\<lambda>x y. x \<sim>\<^sub>Q y"
  by (metis ltln\<^sub>Q.abs_eq_iff)

definition
  eq\<^sub>Q: "equal_class.equal \<equiv> ltln\<^sub>Q_eq_test"

instance
  by (standard; simp add: eq\<^sub>Q ltln\<^sub>Q_eq_test.rep_eq, metis Quotient_ltln\<^sub>Q Quotient_rel_rep)

end

lemma af_letter_unfolding:
  "af_letter (Unf \<phi>) \<nu> \<sim>\<^sub>P af_letter \<phi> \<nu>"
  by (induction \<phi>) (simp_all add: ltl_prop_equiv_def, blast+)

lemma af_letter_prop_unfold_congruent:
  assumes "\<phi> \<sim>\<^sub>Q \<psi>"
  shows "af_letter \<phi> \<nu> \<sim>\<^sub>Q af_letter \<psi> \<nu>"
proof -
  have "Unf \<phi> \<sim>\<^sub>P Unf \<psi>"
    using assms by (simp add: ltl_prop_unfold_equiv_def ltl_prop_equiv_def)
  then have "af_letter (Unf \<phi>) \<nu> \<sim>\<^sub>P af_letter (Unf \<psi>) \<nu>"
    by (simp add: prop_af_congruent.af_letter_congruent)
  then have "af_letter \<phi> \<nu> \<sim>\<^sub>P af_letter \<psi> \<nu>"
    by (metis af_letter_unfolding ltl_prop_equivalence.eq_sym ltl_prop_equivalence.eq_trans)
  then show "af_letter \<phi> \<nu> \<sim>\<^sub>Q af_letter \<psi> \<nu>"
    by (rule ltl_prop_equiv_implies_ltl_prop_unfold_equiv)
qed

lemma GF_advice_prop_unfold_congruent:
  assumes "\<phi> \<sim>\<^sub>Q \<psi>"
  shows "(Unf \<phi>)[X]\<^sub>\<nu> \<sim>\<^sub>Q (Unf \<psi>)[X]\<^sub>\<nu>"
proof -
  have "Unf \<phi> \<sim>\<^sub>P Unf \<psi>"
    using assms
    by (simp add: ltl_prop_unfold_equiv_def ltl_prop_equiv_def)
  then have "(Unf \<phi>)[X]\<^sub>\<nu> \<sim>\<^sub>P (Unf \<psi>)[X]\<^sub>\<nu>"
    by (simp add: GF_advice_prop_congruent(2))
  then show "(Unf \<phi>)[X]\<^sub>\<nu> \<sim>\<^sub>Q (Unf \<psi>)[X]\<^sub>\<nu>"
    by (simp add: ltl_prop_equiv_implies_ltl_prop_unfold_equiv)
qed

interpretation prop_unfold_equivalence: ltl_equivalence "(\<sim>\<^sub>Q)"
  by unfold_locales (metis ltl_prop_unfold_equiv_equivp ltl_prop_unfold_equiv_gt_and_lt)+

interpretation af_congruent "(\<sim>\<^sub>Q)"
  by unfold_locales (rule af_letter_prop_unfold_congruent)

lemma unfolding_monotonic:
  "w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu> \<Longrightarrow> w \<Turnstile>\<^sub>n (Unf \<phi>)[X]\<^sub>\<nu>"
proof (induction \<phi>)
  case (Until_ltln \<phi>1 \<phi>2)
  then show ?case
    by (cases "(\<phi>1 U\<^sub>n \<phi>2) \<in> X") force+
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    using ltln_expand_Release by auto
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
    using ltln_expand_WeakUntil by auto
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)
  then show ?case
    by (cases "(\<phi>1 M\<^sub>n \<phi>2) \<in> X") force+
qed auto

lemma unfolding_next_step_equivalent:
  "w \<Turnstile>\<^sub>n (Unf \<phi>)[X]\<^sub>\<nu> \<Longrightarrow> suffix 1 w \<Turnstile>\<^sub>n (af_letter \<phi> (w 0))[X]\<^sub>\<nu>"
proof (induction \<phi>)
  case (Next_ltln \<phi>)
  then show ?case
    unfolding Unf.simps by (metis GF_advice_af_letter build_split)
next
  case (Until_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding Unf.simps
    by (metis GF_advice.simps(2) GF_advice.simps(3) GF_advice_af_letter af_letter.simps(8) build_split semantics_ltln.simps(5) semantics_ltln.simps(6))
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding Unf.simps
    by (metis GF_advice.simps(2) GF_advice.simps(3) GF_advice_af_letter One_nat_def af_letter.simps(9) build_first semantics_ltln.simps(5) semantics_ltln.simps(6))
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding Unf.simps
    by (metis GF_advice.simps(2) GF_advice.simps(3) GF_advice_af_letter af_letter.simps(10) build_split semantics_ltln.simps(5) semantics_ltln.simps(6))
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding Unf.simps
    by (metis GF_advice.simps(2) GF_advice.simps(3) GF_advice_af_letter af_letter.simps(11) build_split semantics_ltln.simps(5) semantics_ltln.simps(6))
qed auto

lemma nested_prop_atoms_Unf:
  "nested_prop_atoms (Unf \<phi>) \<subseteq> nested_prop_atoms \<phi>"
  by (induction \<phi>) auto

(* TODO move somewhere?? *)
lemma refine_image:
  assumes "\<And>x y. f x = f y \<longrightarrow> g x = g y"
  assumes "finite (f ` X)"
  shows "finite (g ` X)"
  and "card (f ` X) \<ge> card (g ` X)"
proof -
  obtain Y where "Y \<subseteq> X" and "finite Y" and Y_def: "f ` X = f ` Y"
    using assms by (meson finite_subset_image subset_refl)
  moreover
  {
    fix x
    assume "x \<in> X"
    then have "g x \<in> g ` Y"
      by (metis (no_types, hide_lams) \<open>x \<in> X\<close> assms(1) Y_def image_iff)
  }
  then have "g ` X = g ` Y"
    using assms `Y \<subseteq> X` by blast
  ultimately
  show "finite (g ` X)"
    by simp

  from \<open>finite Y\<close> have "card (f ` Y) \<ge> card (g ` Y)"
  proof (induction Y rule: finite_induct)
    case (insert x F)

    then have 1: "finite (g ` F)" and 2: "finite (f ` F)"
      by simp_all

    have "f x \<in> f ` F \<Longrightarrow> g x \<in> g ` F"
      using assms(1) by blast

    then show ?case
      using insert by (simp add: card_insert_if[OF 1] card_insert_if[OF 2])
  qed simp

  then show "card (f ` X) \<ge> card (g ` X)"
    by (simp add: Y_def \<open>g ` X = g ` Y\<close>)
qed

lemma abs_ltln\<^sub>P_implies_abs_ltln\<^sub>Q:
  "abs_ltln\<^sub>P \<phi> = abs_ltln\<^sub>P \<psi> \<longrightarrow> abs_ltln\<^sub>Q \<phi> = abs_ltln\<^sub>Q \<psi>"
  by (simp add: ltl_prop_equiv_implies_ltl_prop_unfold_equiv ltln\<^sub>P.abs_eq_iff ltln\<^sub>Q.abs_eq_iff)

lemmas prop_unfold_equiv_helper = refine_image[of abs_ltln\<^sub>P abs_ltln\<^sub>Q, OF abs_ltln\<^sub>P_implies_abs_ltln\<^sub>Q]

lemma prop_unfold_equiv_finite:
  "finite P \<Longrightarrow> finite {abs_ltln\<^sub>Q \<psi> |\<psi>. prop_atoms \<psi> \<subseteq> P}"
  using prop_unfold_equiv_helper(1)[OF prop_equiv_finite[unfolded image_Collect[symmetric]]]
  unfolding image_Collect[symmetric] .

lemma prop_unfold_equiv_card:
  "finite P \<Longrightarrow> card {abs_ltln\<^sub>Q \<psi> |\<psi>. prop_atoms \<psi> \<subseteq> P} \<le> 2 ^ 2 ^ card P"
  using prop_unfold_equiv_helper(2)[OF prop_equiv_finite[unfolded image_Collect[symmetric]]] prop_equiv_card
  unfolding image_Collect[symmetric]
  by fastforce

lemma Unf_eventually_equivalent:
  "w \<Turnstile>\<^sub>n Unf \<phi>[X]\<^sub>\<nu> \<Longrightarrow> \<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>"
  by (metis (full_types) One_nat_def foldl.simps(1) foldl.simps(2) subsequence_singleton unfolding_next_step_equivalent)

interpretation prop_unfold_GF_advice_compatible: GF_advice_congruent "(\<sim>\<^sub>Q)" Unf
  by unfold_locales (simp_all add: unfolding_prop_unfold_idem prop_unfold_equivalence.eq_sym unfolding_monotonic Unf_eventually_equivalent GF_advice_prop_unfold_congruent)

end