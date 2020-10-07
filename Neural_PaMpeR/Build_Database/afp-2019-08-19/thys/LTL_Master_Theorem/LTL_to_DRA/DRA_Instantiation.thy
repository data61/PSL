(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Instantiation of the LTL to DRA construction\<close>

theory DRA_Instantiation
imports
  DRA_Construction
  LTL.Equivalence_Relations
  "HOL-Library.Log_Nat"
begin

text \<open>We instantiate the construction locale with propositional equivalence
      and obtain a function converting a formula into an abstract automaton.\<close>

global_interpretation ltl_to_dra: dra_construction "(\<sim>\<^sub>P)" rep_ltln\<^sub>P abs_ltln\<^sub>P
  defines ltl_to_dra = ltl_to_dra.ltl_to_dra
    and ltl_to_dra_alphabet = ltl_to_dra.ltl_to_dra_alphabet
    and \<AA>' = ltl_to_dra.\<AA>'
    and \<AA>\<^sub>1 = ltl_to_dra.\<AA>\<^sub>1
    and \<AA>\<^sub>2 = ltl_to_dra.\<AA>\<^sub>2
    and \<AA>\<^sub>3 = ltl_to_dra.\<AA>\<^sub>3
    and \<AA>\<^sub>\<nu>_FG = ltl_to_dra.\<AA>\<^sub>\<nu>_FG
    and \<AA>\<^sub>\<mu>_GF = ltl_to_dra.\<AA>\<^sub>\<mu>_GF
    and af_letter\<^sub>G = ltl_to_dra.af_letter\<^sub>G
    and af_letter\<^sub>F = ltl_to_dra.af_letter\<^sub>F
    and af_letter\<^sub>G_lifted = ltl_to_dra.af_letter\<^sub>G_lifted
    and af_letter\<^sub>F_lifted = ltl_to_dra.af_letter\<^sub>F_lifted
    and af_letter\<^sub>\<nu>_lifted = ltl_to_dra.af_letter\<^sub>\<nu>_lifted
    and \<CC> = ltl_to_dra.\<CC>
    and af_letter\<^sub>\<nu> = ltl_to_dra.af_letter\<^sub>\<nu>
  by unfold_locales (meson Quotient_abs_rep Quotient_ltln\<^sub>P, simp add: Quotient_abs_rep Quotient_ltln\<^sub>P ltln\<^sub>P.abs_eq_iff)

text \<open>We obtain the following theorem:\<close>

thm ltl_to_dra.ltl_to_dra_language


text \<open>Furthermore, we verify the size bound of the automaton to be double-exponential.\<close>

lemma prop_equiv_nested_prop_atoms_finite:
  "finite {abs_ltln\<^sub>P \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  using prop_equiv_finite'[OF nested_prop_atoms_finite] .

lemma prop_equiv_nested_prop_atoms_card:
  "card {abs_ltln\<^sub>P \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>} \<le> 2 ^ 2 ^ card (nested_prop_atoms \<phi>)"
  using prop_equiv_card'[OF nested_prop_atoms_finite] .


lemma prop_equiv_nested_prop_atoms\<^sub>\<nu>_finite:
  "finite {abs_ltln\<^sub>P \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X}"
  using prop_equiv_finite'[OF nested_prop_atoms\<^sub>\<nu>_finite] by fast

lemma prop_equiv_nested_prop_atoms\<^sub>\<nu>_card:
  "card {abs_ltln\<^sub>P \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X} \<le> 2 ^ 2 ^ card (nested_prop_atoms \<phi>)" (is "?lhs \<le> ?rhs")
proof -
  have "finite {abs_ltln\<^sub>P \<psi> | \<psi>. prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X}"
    by (simp add: prop_equiv_nested_prop_atoms\<^sub>\<nu>_finite nested_prop_atoms\<^sub>\<nu>_finite prop_equiv_finite)

  then have "?lhs \<le> card {abs_ltln\<^sub>P \<psi> | \<psi>. prop_atoms \<psi> \<subseteq> (nested_prop_atoms\<^sub>\<nu> \<phi> X)}"
    using card_mono prop_equiv_subset by blast

  also have "\<dots> \<le> 2 ^ 2 ^ card (nested_prop_atoms\<^sub>\<nu> \<phi> X)"
    using prop_equiv_card[OF nested_prop_atoms\<^sub>\<nu>_finite] by fast

  also have "\<dots> \<le> ?rhs"
    using nested_prop_atoms\<^sub>\<nu>_card by auto

  finally show ?thesis .
qed


lemma \<AA>\<^sub>\<mu>_GF_nodes_finite:
  "finite (DBA.nodes (\<AA>\<^sub>\<mu>_GF \<phi>))"
  using finite_subset[OF ltl_to_dra.\<AA>\<^sub>\<mu>_GF_nodes prop_equiv_nested_prop_atoms_finite] .

lemma \<AA>\<^sub>\<nu>_FG_nodes_finite:
  "finite (DCA.nodes (\<AA>\<^sub>\<nu>_FG \<phi>))"
  using finite_subset[OF ltl_to_dra.\<AA>\<^sub>\<nu>_FG_nodes prop_equiv_nested_prop_atoms_finite] .

lemma \<AA>\<^sub>\<mu>_GF_nodes_card:
  "card (DBA.nodes (\<AA>\<^sub>\<mu>_GF \<phi>)) \<le> 2 ^ 2 ^ card (nested_prop_atoms (F\<^sub>n \<phi>))"
  using le_trans[OF card_mono[OF prop_equiv_nested_prop_atoms_finite ltl_to_dra.\<AA>\<^sub>\<mu>_GF_nodes] prop_equiv_nested_prop_atoms_card] .

lemma \<AA>\<^sub>\<nu>_FG_nodes_card:
  "card (DCA.nodes (\<AA>\<^sub>\<nu>_FG \<phi>)) \<le> 2 ^ 2 ^ card (nested_prop_atoms (G\<^sub>n \<phi>))"
  using le_trans[OF card_mono[OF prop_equiv_nested_prop_atoms_finite ltl_to_dra.\<AA>\<^sub>\<nu>_FG_nodes] prop_equiv_nested_prop_atoms_card] .


lemma \<AA>\<^sub>2_nodes_finite_helper:
  "list_all (finite \<circ> DBA.nodes) (map (\<lambda>\<psi>. \<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>)) xs)"
  by (auto simp: list.pred_map list_all_iff \<AA>\<^sub>\<mu>_GF_nodes_finite)

lemma \<AA>\<^sub>2_nodes_finite:
  "finite (DBA.nodes (\<AA>\<^sub>2 xs ys))"
  unfolding ltl_to_dra.\<AA>\<^sub>2_def using dbail_nodes_finite \<AA>\<^sub>2_nodes_finite_helper .

lemma \<AA>\<^sub>3_nodes_finite_helper:
  "list_all (finite \<circ> DCA.nodes) (map (\<lambda>\<psi>. \<AA>\<^sub>\<nu>_FG (\<psi>[set xs]\<^sub>\<nu>)) ys)"
  by (auto simp: list.pred_map list_all_iff \<AA>\<^sub>\<nu>_FG_nodes_finite)

lemma \<AA>\<^sub>3_nodes_finite:
  "finite (DCA.nodes (\<AA>\<^sub>3 xs ys))"
  unfolding ltl_to_dra.\<AA>\<^sub>3_def using dcail_finite \<AA>\<^sub>3_nodes_finite_helper .

(* TODO add to HOL/Groups_List.thy *)
lemma list_prod_mono:
  "f \<le> g \<Longrightarrow> (\<Prod>x\<leftarrow>xs. f x) \<le> (\<Prod>x\<leftarrow>xs. g x)" for f g :: "'a \<Rightarrow> nat"
  by (induction xs) (auto simp: le_funD mult_le_mono)

(* TODO add to HOL/Groups_List.thy *)
lemma list_prod_const:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> c) \<Longrightarrow> (\<Prod>x\<leftarrow>xs. f x) \<le> c ^ length xs" for f :: "'a \<Rightarrow> nat"
  by (induction xs) (auto simp: mult_le_mono)

(* TODO add to HOL/Finite_Set.thy *)
lemma card_insert_Suc:
  "card (insert x S) \<le> Suc (card S)"
  by (metis Suc_n_not_le_n card.infinite card_insert_if finite_insert linear)

(* TODO add to HOL/Power.thy *)
lemma nat_power_le_imp_le:
  "0 < a \<Longrightarrow> a \<le> b \<Longrightarrow> x ^ a \<le> x ^ b" for x :: nat
  by (metis leD linorder_le_less_linear nat_power_less_imp_less neq0_conv power_eq_0_iff)

(* TODO add to HOL/Power.thy *)
lemma const_less_power:
  "n < x ^ n" if "x > 1"
  using that by (induction n) (auto simp: less_trans_Suc)

(* TODO add to HOL-Library/Log_Nat.thy *)
lemma floorlog_le_const:
  "floorlog x n \<le> n"
  by (induction n) (simp add: floorlog_eq_zero_iff, metis Suc_lessI floorlog_le_iff le_SucI power_inject_exp)

lemma \<AA>\<^sub>2_nodes_card:
  assumes
    "length xs \<le> n"
  and
    "\<And>\<psi>. \<psi> \<in> set xs \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
  shows
    "card (DBA.nodes (\<AA>\<^sub>2 xs ys)) \<le> 2 ^ 2 ^ (n + floorlog 2 n + 2)"
proof -
  have 1: "\<And>\<psi>. \<psi> \<in> set xs \<Longrightarrow> card (nested_prop_atoms (F\<^sub>n \<psi>[set ys]\<^sub>\<mu>)) \<le> Suc n"
  proof -
    fix \<psi>
    assume "\<psi> \<in> set xs"

    have "card (nested_prop_atoms (F\<^sub>n (\<psi>[set ys]\<^sub>\<mu>)))
          \<le> Suc (card (nested_prop_atoms (\<psi>[set ys]\<^sub>\<mu>)))"
      by (simp add: card_insert_Suc)

    also have "\<dots> \<le> Suc (card (nested_prop_atoms \<psi>))"
      by (simp add: FG_advice_nested_prop_atoms_card)

    also have "\<dots> \<le> Suc n"
      by (simp add: assms(2) \<open>\<psi> \<in> set xs\<close>)

    finally show "card (nested_prop_atoms (F\<^sub>n (\<psi>[set ys]\<^sub>\<mu>))) \<le> Suc n" .
  qed

  have "(\<Prod>\<psi>\<leftarrow>xs. card (DBA.nodes (\<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>))))
        \<le> (\<Prod>\<psi>\<leftarrow>xs. 2 ^ 2 ^ card (nested_prop_atoms (F\<^sub>n (\<psi>[set ys]\<^sub>\<mu>))))"
    by (rule list_prod_mono) (insert \<AA>\<^sub>\<mu>_GF_nodes_card le_fun_def, blast)

  also have "\<dots> \<le> (2 ^ 2 ^ Suc n) ^ length xs"
    by (rule list_prod_const) (metis 1 Suc_leI nat_power_le_imp_le nat_power_eq_Suc_0_iff neq0_conv pos2 zero_less_power)

  also have "\<dots> \<le> (2 ^ 2 ^ Suc n) ^ n"
    using assms(1) nat_power_le_imp_le by fastforce

  also have "\<dots> = 2 ^ (n * 2 ^ Suc n)"
    by (metis Groups.mult_ac(2) power_mult)

  also have "\<dots> \<le> 2 ^ (2 ^ floorlog 2 n * 2 ^ Suc n)"
    by (cases "n = 0") (auto simp: floorlog_bounds less_imp_le_nat)

  also have "\<dots> = 2 ^ 2 ^ (Suc n + floorlog 2 n)"
    by (simp add: power_add)

  finally have 2: "(\<Prod>\<psi>\<leftarrow>xs. card (DBA.nodes (\<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>)))) \<le> 2 ^ 2 ^ (Suc n + floorlog 2 n)" .

  have "card (DBA.nodes (\<AA>\<^sub>2 xs ys)) \<le> max 1 (length xs) * (\<Prod>\<psi>\<leftarrow>xs. card (DBA.nodes (\<AA>\<^sub>\<mu>_GF (\<psi>[set ys]\<^sub>\<mu>))))"
    using dbail_nodes_card[OF \<AA>\<^sub>2_nodes_finite_helper]
    by (auto simp: ltl_to_dra.\<AA>\<^sub>2_def comp_def)

  also have "\<dots> \<le> max 1 n * 2 ^ 2 ^ (Suc n + floorlog 2 n)"
    using assms(1) 2 by (simp add: mult_le_mono)

  also have "\<dots> \<le> 2 ^ (floorlog 2 n) * 2 ^ 2 ^ (Suc n + floorlog 2 n)"
    by (cases "n = 0") (auto simp: floorlog_bounds less_imp_le_nat)

  also have "\<dots> = 2 ^ (floorlog 2 n + 2 ^ (Suc n + floorlog 2 n))"
    by (simp add: power_add)

  also have "\<dots> \<le> 2 ^ (n + 2 ^ (Suc n + floorlog 2 n))"
    by (simp add: floorlog_le_const)

  also have "\<dots> \<le> 2 ^ 2 ^ (n + floorlog 2 n + 2)"
    by simp (metis const_less_power Suc_1 add_Suc_right add_leE lessI less_imp_le_nat power_Suc)

  finally show ?thesis .
qed


lemma \<AA>\<^sub>3_nodes_card:
  assumes
    "length ys \<le> n"
  and
    "\<And>\<psi>. \<psi> \<in> set ys \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
  shows
    "card (DCA.nodes (\<AA>\<^sub>3 xs ys)) \<le> 2 ^ 2 ^ (n + floorlog 2 n + 1)"
proof -
  have 1: "\<And>\<psi>. \<psi> \<in> set ys \<Longrightarrow> card (DCA.nodes (\<AA>\<^sub>\<nu>_FG (\<psi>[set xs]\<^sub>\<nu>))) \<le> 2 ^ 2 ^ Suc n"
  proof -
    fix \<psi>
    assume "\<psi> \<in> set ys"

    have "card (nested_prop_atoms (G\<^sub>n \<psi>[set xs]\<^sub>\<nu>))
          \<le> Suc (card (nested_prop_atoms (\<psi>[set xs]\<^sub>\<nu>)))"
      by (simp add: card_insert_Suc)

    also have "\<dots> \<le> Suc (card (nested_prop_atoms \<psi>))"
      by (simp add: GF_advice_nested_prop_atoms_card)

    also have "\<dots> \<le> Suc n"
      by (simp add: assms(2) \<open>\<psi> \<in> set ys\<close>)

    finally have 2: "card (nested_prop_atoms (G\<^sub>n \<psi>[set xs]\<^sub>\<nu>)) \<le> Suc n" .

    then show "?thesis \<psi>"
      by (intro le_trans[OF \<AA>\<^sub>\<nu>_FG_nodes_card]) (meson one_le_numeral power_increasing)
  qed


  have "card (DCA.nodes (\<AA>\<^sub>3 xs ys)) \<le> (\<Prod>\<psi>\<leftarrow>ys. card (DCA.nodes (\<AA>\<^sub>\<nu>_FG (\<psi>[set xs]\<^sub>\<nu>))))"
    unfolding ltl_to_dra.\<AA>\<^sub>3_def using dcail_nodes_card[OF \<AA>\<^sub>3_nodes_finite_helper]
    by (auto simp: comp_def)

  also have "\<dots> \<le> (2 ^ 2 ^ Suc n) ^ length ys"
    by (rule list_prod_const) (rule 1)

  also have "\<dots> \<le> (2 ^ 2 ^ Suc n) ^ n"
    by (simp add: assms(1) power_increasing)

  also have "\<dots> \<le> 2 ^ (n * 2 ^ Suc n)"
    by (metis le_refl mult.commute power_mult)

  also have "\<dots> \<le> 2 ^ (2 ^ floorlog 2 n * 2 ^ Suc n)"
    by (cases \<open>n > 0\<close>) (simp_all add: floorlog_bounds less_imp_le_nat)

  also have "\<dots> = 2 ^ 2 ^ (n + floorlog 2 n + 1)"
    by (simp add: power_add)

  finally show ?thesis .
qed


lemma \<AA>\<^sub>1_nodes_finite:
  "finite (DCA.nodes (\<AA>\<^sub>1 \<phi> xs))"
  unfolding ltl_to_dra.\<AA>\<^sub>1_def
  by (metis (no_types, lifting) finite_subset ltl_to_dra.\<CC>_nodes finite_SigmaI prop_equiv_nested_prop_atoms\<^sub>\<nu>_finite prop_equiv_nested_prop_atoms_finite)

lemma \<AA>\<^sub>1_nodes_card:
  assumes
    "card (subfrmlsn \<phi>) \<le> n"
  shows
    "card (DCA.nodes (\<AA>\<^sub>1 \<phi> xs)) \<le> 2 ^ 2 ^ (n + 1)"
proof -
  let ?fst = "{abs_ltln\<^sub>P \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms \<phi>}"
  let ?snd = "{abs_ltln\<^sub>P \<psi> | \<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> (set xs)}"

  have 1: "card (nested_prop_atoms \<phi>) \<le> n"
    by (meson card_mono[OF subfrmlsn_finite nested_prop_atoms_subfrmlsn] assms le_trans)


  have "card (DCA.nodes (\<AA>\<^sub>1 \<phi> xs)) \<le> card (?fst \<times> ?snd)"
    unfolding ltl_to_dra.\<AA>\<^sub>1_def
    by (rule card_mono) (simp_all add: ltl_to_dra.\<CC>_nodes prop_equiv_nested_prop_atoms\<^sub>\<nu>_finite prop_equiv_nested_prop_atoms_finite)

  also have "\<dots> = card ?fst * card ?snd"
    using prop_equiv_nested_prop_atoms\<^sub>\<nu>_finite card_cartesian_product by blast

  also have "\<dots> \<le> 2 ^ 2 ^ card (nested_prop_atoms \<phi>) * 2 ^ 2 ^ card (nested_prop_atoms \<phi>)"
    using prop_equiv_nested_prop_atoms\<^sub>\<nu>_card prop_equiv_nested_prop_atoms_card mult_le_mono by blast

  also have "\<dots> = 2 ^ 2 ^ (card (nested_prop_atoms \<phi>) + 1)"
    by (simp add: semiring_normalization_rules(36))

  also have "\<dots> \<le> 2 ^ 2 ^ (n + 1)"
    using assms 1 by simp

  finally show ?thesis .
qed


lemma \<AA>'_nodes_finite:
  "finite (DRA.nodes (\<AA>' \<phi> xs ys))"
  unfolding ltl_to_dra.\<AA>'_def
  using dcai_nodes_finite dbcrai_nodes_finite
  using \<AA>\<^sub>1_nodes_finite \<AA>\<^sub>2_nodes_finite \<AA>\<^sub>3_nodes_finite
  by fast

lemma \<AA>'_nodes_card:
  assumes
    "length xs \<le> n"
  and
    "\<And>\<psi>. \<psi> \<in> set xs \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
  and
    "length ys \<le> n"
  and
    "\<And>\<psi>. \<psi> \<in> set ys \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
  and
    "card (subfrmlsn \<phi>) \<le> n"
  shows
    "card (DRA.nodes (\<AA>' \<phi> xs ys)) \<le> 2 ^ 2 ^ (n + floorlog 2 n + 4)"
proof -
  have "n + 1 \<le> n + floorlog 2 n + 2"
    by auto

  then have 1: "(2::nat) ^ (n + 1) \<le> 2 ^ (n + floorlog 2 n + 2)"
    using one_le_numeral power_increasing by blast


  have "card (DRA.nodes (\<AA>' \<phi> xs ys)) \<le> card (DCA.nodes (\<AA>\<^sub>1 \<phi> xs)) * card (DBA.nodes (\<AA>\<^sub>2 xs ys)) * card (DCA.nodes (\<AA>\<^sub>3 xs ys))" (is "?lhs \<le> ?rhs")
  proof (unfold ltl_to_dra.\<AA>'_def)
    have "card (DBA.nodes (\<AA>\<^sub>2 xs ys)) * card (DCA.nodes (dcai (\<AA>\<^sub>1 \<phi> xs) (\<AA>\<^sub>3 xs ys))) \<le> ?rhs"
      by (simp add: dcai_nodes_card[OF \<AA>\<^sub>1_nodes_finite \<AA>\<^sub>3_nodes_finite])
    then show "card (DRA.nodes (dbcrai (\<AA>\<^sub>2 xs ys) (dcai (\<AA>\<^sub>1 \<phi> xs) (\<AA>\<^sub>3 xs ys)))) \<le> ?rhs"
      by (meson dbcrai_nodes_card[OF \<AA>\<^sub>2_nodes_finite dcai_nodes_finite[OF \<AA>\<^sub>1_nodes_finite \<AA>\<^sub>3_nodes_finite]] basic_trans_rules(23))
  qed

  also have "\<dots> \<le> 2 ^ 2 ^ (n + 1) * 2 ^ 2 ^ (n + floorlog 2 n + 2) * 2 ^ 2 ^ (n + floorlog 2 n + 1)"
    using \<AA>\<^sub>1_nodes_card[OF assms(5)] \<AA>\<^sub>2_nodes_card[OF assms(1,2)] \<AA>\<^sub>3_nodes_card[OF assms(3,4)]
    by (metis mult_le_mono)

  also have "\<dots> = 2 ^ (2 ^ (n + 1) + 2 ^ (n + floorlog 2 n + 2) + 2 ^ (n + floorlog 2 n + 1))"
    by (metis power_add)

  also have "\<dots> \<le> 2 ^ (4 * 2 ^ (n + floorlog 2 n + 2))"
    using 1 by auto

  finally show ?thesis
    by (simp add: numeral.simps(2) power_add)
qed

lemma subformula_nested_prop_atoms_subfrmlsn:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> nested_prop_atoms \<psi> \<subseteq> subfrmlsn \<phi>"
  using nested_prop_atoms_subfrmlsn subfrmlsn_subset by blast


lemma ltl_to_dra_nodes_finite:
  "finite (DRA.nodes (ltl_to_dra \<phi>))"
  unfolding ltl_to_dra.ltl_to_dra_def
  apply (rule draul_nodes_finite)
  apply (simp add: split_def ltl_to_dra.\<AA>'_alphabet advice_sets_not_empty)
  apply (simp add: list.pred_set split_def \<AA>'_nodes_finite)
  done

lemma ltl_to_dra_nodes_card:
  assumes
    "card (subfrmlsn \<phi>) \<le> n"
  shows
    "card (DRA.nodes (ltl_to_dra \<phi>)) \<le> 2 ^ 2 ^ (2 * n + floorlog 2 n + 4)"
proof -
  let ?map = "map (\<lambda>(x, y). \<AA>' \<phi> x y) (advice_sets \<phi>)"

  have 1: "\<And>x::nat. x > 0 \<Longrightarrow> x ^ length (advice_sets \<phi>) \<le> x ^ 2 ^ card (subfrmlsn \<phi>)"
    by (metis advice_sets_length linorder_not_less nat_power_less_imp_less)

  have "card (DRA.nodes (ltl_to_dra \<phi>)) \<le> prod_list (map (card \<circ> DRA.nodes) ?map)"
    unfolding ltl_to_dra.ltl_to_dra_def
    apply (rule draul_nodes_card)
    unfolding set_map image_image split_def ltl_to_dra.\<AA>'_alphabet
    apply (simp add: advice_sets_not_empty)
    unfolding split_def list.pred_set using \<AA>'_nodes_finite by auto

  also have "\<dots> = (\<Prod>(x, y)\<leftarrow>advice_sets \<phi>. card (DRA.nodes (\<AA>' \<phi> x y)))"
    by (induction "advice_sets \<phi>") (auto, metis (no_types, lifting) comp_apply split_def)

  also have "\<dots> \<le> (2 ^ 2 ^ (n + floorlog 2 n + 4)) ^ length (advice_sets \<phi>)"
  proof (rule list_prod_const, unfold split_def, rule \<AA>'_nodes_card)
    show "\<And>x. x \<in> set (advice_sets \<phi>) \<Longrightarrow> length (fst x) \<le> n"
      using advice_sets_element_length assms by fastforce

    show "\<And>x \<psi>. \<lbrakk>x \<in> set (advice_sets \<phi>); \<psi> \<in> set (fst x)\<rbrakk> \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
      using advice_sets_element_subfrmlsn(1) assms subformula_nested_prop_atoms_subfrmlsn subformulas\<^sub>\<mu>_subfrmlsn
      by (metis (no_types, lifting) card_mono subfrmlsn_finite subset_iff sup.absorb_iff2 sup.coboundedI1 surjective_pairing)

    show "\<And>x. x \<in> set (advice_sets \<phi>) \<Longrightarrow> length (snd x) \<le> n"
      using advice_sets_element_length assms by fastforce

    show "\<And>x \<psi>. \<lbrakk>x \<in> set (advice_sets \<phi>); \<psi> \<in> set (snd x)\<rbrakk> \<Longrightarrow> card (nested_prop_atoms \<psi>) \<le> n"
      using advice_sets_element_subfrmlsn(2) assms subformula_nested_prop_atoms_subfrmlsn subformulas\<^sub>\<nu>_subfrmlsn
      by (metis (no_types, lifting) card_mono subfrmlsn_finite subset_iff sup.absorb_iff2 sup.coboundedI1 surjective_pairing)
  qed (insert assms, blast)

  also have "\<dots> \<le> (2 ^ 2 ^ (n + floorlog 2 n + 4)) ^ (2 ^ card (subfrmlsn \<phi>))"
    by (simp add: 1)

  also have "\<dots> \<le> (2 ^ 2 ^ (n + floorlog 2 n + 4)) ^ (2 ^ n)"
    by (simp add: assms power_increasing)

  also have "\<dots> = 2 ^ (2 ^ n * 2 ^ (n + floorlog 2 n + 4))"
    by (metis Rat.sign_simps(5) power_mult)

  also have "\<dots> = 2 ^ 2 ^ (2 * n + floorlog 2 n + 4)"
    by (simp add: semiring_normalization_rules(26))

  finally show ?thesis .
qed

theorem ltl_to_dra_size:
  "card (DRA.nodes (ltl_to_dra \<phi>)) \<le> 2 ^ 2 ^ (2 * size \<phi> + floorlog 2 (size \<phi>) + 4)"
  using ltl_to_dra_nodes_card subfrmlsn_card by blast

end
