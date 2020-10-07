(* License: LGPL *)
(* Author: Julian Parsert *)

theory Lotteries
  imports
    PMF_Composition
    "HOL-Probability.Probability"
begin


section \<open> Lotteries \<close>

definition lotteries_on 
  where
    "lotteries_on Oc = {p . (set_pmf p) \<subseteq> Oc}"

lemma lotteries_on_subset:
  assumes "A \<subseteq> B"
  shows "lotteries_on A \<subseteq> lotteries_on B"
  by (metis (no_types, lifting) Collect_mono assms gfp.leq_trans lotteries_on_def)

lemma support_in_outcomes:
  "\<forall>oc. \<forall>p \<in> lotteries_on oc. \<forall>a \<in> set_pmf p. a \<in> oc"
  by (simp add: lotteries_on_def subsetD)

lemma lotteries_on_nonempty:
  assumes "outcomes \<noteq> {}" 
  shows "lotteries_on outcomes \<noteq> {}"
  by (auto simp: lotteries_on_def) (metis (full_types) assms 
      empty_subsetI ex_in_conv insert_subset set_return_pmf)

lemma finite_support_one_oc:
  assumes "card outcomes = 1"
  shows "\<forall>l \<in> lotteries_on outcomes. finite (set_pmf l)"
  by (metis assms card_infinite finite_subset lotteries_on_def mem_Collect_eq zero_neq_one)

lemma one_outcome_card_support_1:
  assumes "card outcomes = 1"
  shows "\<forall>l \<in> lotteries_on outcomes. card (set_pmf l) = 1"
proof 
  fix l
  assume "l \<in> lotteries_on outcomes"
  have "finite outcomes"
    using assms card_infinite by force
  then have "l \<in> lotteries_on outcomes \<longrightarrow> 1 = card (set_pmf l)"
    by (metis assms card_eq_0_iff card_mono finite_support_one_oc le_neq_implies_less 
        less_one lotteries_on_def mem_Collect_eq set_pmf_not_empty)
  then show "card (set_pmf l) = 1"
    by (simp add: \<open>l \<in> lotteries_on outcomes\<close>)
qed  

lemma finite_nempty_ex_degernate_in_lotteries:
  assumes "out \<noteq> {}"
  assumes "finite out"
  shows "\<exists>e \<in> lotteries_on out. \<exists>x \<in> out. pmf e x = 1"
proof (rule ccontr)
  assume a: "\<not> (\<exists>e\<in>lotteries_on out. \<exists>x\<in>out. pmf e x = 1)"
  then have subset: "\<forall>e \<in> lotteries_on out. set_pmf e \<subseteq> out"
    using lotteries_on_def by (simp add: lotteries_on_def)
  then have "\<forall>e. e \<in> lotteries_on out \<longrightarrow> ((\<Sum>i\<in>set_pmf e. pmf e i) = 1)"
    using sum_pmf_eq_1 by (metis subset  assms(2) finite_subset order_refl)
  then show False
    by (metis (no_types, lifting) a assms(1) assms(2) card_empty card_gt_0_iff card_seteq 
        empty_subsetI finite.emptyI finite_insert insert_subset lotteries_on_def subsetI
        measure_measure_pmf_finite mem_Collect_eq nat_less_le pmf.rep_eq set_pmf_of_set )
qed

lemma card_support_1_probability_1:
  assumes "card (set_pmf p) = 1"
  shows "\<forall>e \<in> set_pmf p. pmf p e = 1" 
  by(auto) (metis assms card_1_singletonE card_ge_0_finite 
      card_subset_eq ex_card le_numeral_extra(4) measure_measure_pmf_finite 
      pmf.rep_eq singletonD sum_pmf_eq_1 zero_less_one)

lemma one_outcome_card_lotteries_1:
  assumes "card outcomes = 1"
  shows "card (lotteries_on outcomes) = 1"
proof -
  obtain x :: 'a where
    x: "outcomes = {x}"
    using assms card_1_singletonE by blast
  have exl: "\<exists>l \<in> lotteries_on outcomes. pmf l x = 1"
    by (metis x assms card_infinite empty_iff 
        finite_nempty_ex_degernate_in_lotteries insert_iff zero_neq_one)
  have pmfs: "\<forall>l \<in> lotteries_on outcomes. set_pmf l = {x}"
    by (simp add: lotteries_on_def set_pmf_subset_singleton x)
  have "\<forall>l \<in> lotteries_on outcomes. pmf l x = 1"
    by (simp add: lotteries_on_def set_pmf_subset_singleton x)
  then show ?thesis 
    by (metis exl empty_iff is_singletonI' is_singleton_altdef
        order_refl pmfs set_pmf_subset_singleton)
qed

lemma return_pmf_card_equals_set:
  shows "card {return_pmf x |x. x \<in> S} = card S"
proof-
  have "{return_pmf x |x. x \<in> S} = return_pmf ` S" 
    by blast
  also have "card \<dots> = card S" 
    by (intro card_image) (auto simp: inj_on_def)
  finally show "card {return_pmf x |x. x \<in> S} = card S" .
qed

lemma mix_pmf_in_lotteries:
  assumes "p \<in> lotteries_on A"
    and "q \<in> lotteries_on A"
    and "a \<in> {0<..<1}"
  shows "(mix_pmf a p q) \<in> lotteries_on A"
proof -
  have "set_pmf (mix_pmf a p q) = set_pmf p \<union> set_pmf q"
    by (meson assms(3) set_pmf_mix)
  then show ?thesis
    by (metis Un_subset_iff assms(1) assms(2) lotteries_on_def mem_Collect_eq)
qed

lemma card_degen_lotteries_equals_outcomes:
  shows "card {x \<in> lotteries_on out. card (set_pmf x) = 1} = card out"
proof -
  consider (empty) "out = {}" | (not_empty) "out \<noteq> {}"
    by blast
  then show ?thesis
  proof (cases)
    case not_empty
    define DG where
      DG: "DG = {x \<in> lotteries_on out. card (set_pmf x) = 1}"
    define AP where
      AP: "AP = {return_pmf x |x. x \<in> out}"
    have **: "card AP = card out"
      using AP return_pmf_card_equals_set by blast
    have *: "\<forall>d \<in> DG. d \<in> AP"
    proof
      fix l
      assume "l \<in> DG"
      then have "l \<in> lotteries_on out \<and> 1 = card (set_pmf l)"
        using DG by force
      then obtain x where
        x: "x \<in> out" "set_pmf l = {x}"
        by (metis (no_types) card_1_singletonE singletonI support_in_outcomes)
      have "return_pmf x = l"
        using set_pmf_subset_singleton x(2) by fastforce
      then show "l \<in> AP" 
        using AP x(1) by blast
    qed
    moreover have "AP = DG"
    proof
      have "\<forall>e \<in> AP. e \<in> lotteries_on out"
        by(auto simp: lotteries_on_def AP)
      then show "AP \<subseteq> DG" using DG AP by force
    qed (auto simp: *)
    ultimately show ?thesis
      using DG ** by blast
  qed (simp add: lotteries_on_def set_pmf_not_empty)
qed

end
