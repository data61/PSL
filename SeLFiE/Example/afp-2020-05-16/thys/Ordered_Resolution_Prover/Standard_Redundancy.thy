(*  Title:       The Standard Redundancy Criterion
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>The Standard Redundancy Criterion\<close>

theory Standard_Redundancy
  imports Proving_Process
begin

text \<open>
This material is based on Section 4.2.2 (``The Standard Redundancy Criterion'') of Bachmair and
Ganzinger's chapter.
\<close>

locale standard_redundancy_criterion =
  inference_system \<Gamma> for \<Gamma> :: "('a :: wellorder) inference set"
begin

(* FIXME: Make a definition *)
abbreviation redundant_infer :: "'a clause set \<Rightarrow> 'a inference \<Rightarrow> bool" where
  "redundant_infer N \<gamma> \<equiv>
   \<exists>DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD + side_prems_of \<gamma> \<longrightarrow> I \<Turnstile> concl_of \<gamma>)
      \<and> (\<forall>D. D \<in># DD \<longrightarrow> D < main_prem_of \<gamma>)"

definition Rf :: "'a clause set \<Rightarrow> 'a clause set" where
  "Rf N = {C. \<exists>DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>D. D \<in># DD \<longrightarrow> D < C)}"

definition Ri :: "'a clause set \<Rightarrow> 'a inference set" where
  "Ri N = {\<gamma> \<in> \<Gamma>. redundant_infer N \<gamma>}"

lemma tautology_redundant:
  assumes "Pos A \<in># C"
  assumes "Neg A \<in># C"
  shows "C \<in> Rf N"
proof -
  have "set_mset {#} \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m {#} \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>D. D \<in># {#} \<longrightarrow> D < C)"
    using assms by auto
  then show "C \<in> Rf N"
    unfolding Rf_def by blast
qed

lemma contradiction_Rf: "{#} \<in> N \<Longrightarrow> Rf N = UNIV - {{#}}"
  unfolding Rf_def by force

text \<open>
The following results correspond to Lemma 4.5. The lemma \<open>wlog_non_Rf\<close> generalizes the core of
the argument.
\<close>

lemma Rf_mono: "N \<subseteq> N' \<Longrightarrow> Rf N \<subseteq> Rf N'"
  unfolding Rf_def by auto

lemma wlog_non_Rf:
  assumes ex: "\<exists>DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>D'. D' \<in># DD \<longrightarrow> D' < D)"
  shows "\<exists>DD. set_mset DD \<subseteq> N - Rf N \<and> (\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>D'. D' \<in># DD \<longrightarrow> D' < D)"
proof -
  from ex obtain DD0 where
    dd0: "DD0 \<in> {DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>D'. D' \<in># DD \<longrightarrow> D' < D)}"
    by blast
  have "\<exists>DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>D'. D' \<in># DD \<longrightarrow> D' < D) \<and>
      (\<forall>DD'. set_mset DD' \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD' + CC \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>D'. D' \<in># DD' \<longrightarrow> D' < D) \<longrightarrow>
    DD \<le> DD')"
    using wf_eq_minimal[THEN iffD1, rule_format, OF wf_less_multiset dd0]
    unfolding not_le[symmetric] by blast
  then obtain DD where
    dd_subs_n: "set_mset DD \<subseteq> N" and
    ddcc_imp_e: "\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> E" and
    dd_lt_d: "\<forall>D'. D' \<in># DD \<longrightarrow> D' < D" and
    d_min: "\<forall>DD'. set_mset DD' \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD' + CC \<longrightarrow> I \<Turnstile> E) \<and> (\<forall>D'. D' \<in># DD' \<longrightarrow> D' < D) \<longrightarrow>
      DD \<le> DD'"
    by blast

  have "\<forall>Da. Da \<in># DD \<longrightarrow> Da \<notin> Rf N"
  proof clarify
    fix Da
    assume
      da_in_dd: "Da \<in># DD" and
      da_rf: "Da \<in> Rf N"

    from da_rf obtain DD' where
      dd'_subs_n: "set_mset DD' \<subseteq> N" and
      dd'_imp_da: "\<forall>I. I \<Turnstile>m DD' \<longrightarrow> I \<Turnstile> Da" and
      dd'_lt_da: "\<forall>D'. D' \<in># DD' \<longrightarrow> D' < Da"
      unfolding Rf_def by blast

    define DDa where
      "DDa = DD - {#Da#} + DD'"

    have "set_mset DDa \<subseteq> N"
      unfolding DDa_def using dd_subs_n dd'_subs_n
      by (meson contra_subsetD in_diffD subsetI union_iff)
    moreover have "\<forall>I. I \<Turnstile>m DDa + CC \<longrightarrow> I \<Turnstile> E"
      using dd'_imp_da ddcc_imp_e da_in_dd unfolding DDa_def true_cls_mset_def
      by (metis in_remove1_mset_neq union_iff)
    moreover have "\<forall>D'. D' \<in># DDa \<longrightarrow> D' < D"
      using dd_lt_d dd'_lt_da da_in_dd unfolding DDa_def
      by (metis insert_DiffM2 order.strict_trans union_iff)
    moreover have "DDa < DD"
      unfolding DDa_def
      by (meson da_in_dd dd'_lt_da mset_lt_single_right_iff single_subset_iff union_le_diff_plus)
    ultimately show False
      using d_min unfolding less_eq_multiset_def by (auto intro!: antisym)
  qed
  then show ?thesis
    using dd_subs_n ddcc_imp_e dd_lt_d by auto
qed

lemma Rf_imp_ex_non_Rf:
  assumes "C \<in> Rf N"
  shows "\<exists>CC. set_mset CC \<subseteq> N - Rf N \<and> (\<forall>I. I \<Turnstile>m CC \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>C'. C' \<in># CC \<longrightarrow> C' < C)"
  using assms by (auto simp: Rf_def intro: wlog_non_Rf[of _ "{#}", simplified])

lemma Rf_subs_Rf_diff_Rf: "Rf N \<subseteq> Rf (N - Rf N)"
proof
  fix C
  assume c_rf: "C \<in> Rf N"
  then obtain CC where
    cc_subs: "set_mset CC \<subseteq> N - Rf N" and
    cc_imp_c: "\<forall>I. I \<Turnstile>m CC \<longrightarrow> I \<Turnstile> C" and
    cc_lt_c: "\<forall>C'. C' \<in># CC \<longrightarrow> C' < C"
    using Rf_imp_ex_non_Rf by blast
  have "\<forall>D. D \<in># CC \<longrightarrow> D \<notin> Rf N"
    using cc_subs by (simp add: subset_iff)
  then have cc_nr:
    "\<And>C DD. C \<in># CC \<Longrightarrow> set_mset DD \<subseteq> N \<Longrightarrow> \<forall>I. I \<Turnstile>m DD \<longrightarrow> I \<Turnstile> C \<Longrightarrow> \<exists>D. D \<in># DD \<and> ~ D < C"
      unfolding Rf_def by auto metis
  have "set_mset CC \<subseteq> N"
    using cc_subs by auto
  then have "set_mset CC \<subseteq> 
    N - {C. \<exists>DD. set_mset DD \<subseteq> N \<and> (\<forall>I. I \<Turnstile>m DD \<longrightarrow> I \<Turnstile> C) \<and> (\<forall>D. D \<in># DD \<longrightarrow> D < C)}"
    using cc_nr by auto
  then show "C \<in> Rf (N - Rf N)"
    using cc_imp_c cc_lt_c unfolding Rf_def by auto
qed

lemma Rf_eq_Rf_diff_Rf: "Rf N = Rf (N - Rf N)"
  by (metis Diff_subset Rf_mono Rf_subs_Rf_diff_Rf subset_antisym)

text \<open>
The following results correspond to Lemma 4.6.
\<close>

lemma Ri_mono: "N \<subseteq> N' \<Longrightarrow> Ri N \<subseteq> Ri N'"
  unfolding Ri_def by auto

lemma Ri_subs_Ri_diff_Rf: "Ri N \<subseteq> Ri (N - Rf N)"
proof
  fix \<gamma>
  assume \<gamma>_ri: "\<gamma> \<in> Ri N"
  then obtain CC D E where \<gamma>: "\<gamma> = Infer CC D E"
    by (cases \<gamma>)
  have cc: "CC = side_prems_of \<gamma>" and d: "D = main_prem_of \<gamma>" and e: "E = concl_of \<gamma>"
    unfolding \<gamma> by simp_all
  obtain DD where
    "set_mset DD \<subseteq> N" and "\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> E" and "\<forall>C. C \<in># DD \<longrightarrow> C < D"
    using \<gamma>_ri unfolding Ri_def cc d e by blast
  then obtain DD' where
    "set_mset DD' \<subseteq> N - Rf N" and "\<forall>I. I \<Turnstile>m DD' + CC \<longrightarrow> I \<Turnstile> E" and "\<forall>D'. D' \<in># DD' \<longrightarrow> D' < D"
    using wlog_non_Rf by atomize_elim blast
  then show "\<gamma> \<in> Ri (N - Rf N)"
    using \<gamma>_ri unfolding Ri_def d cc e by blast
qed

lemma Ri_eq_Ri_diff_Rf: "Ri N = Ri (N - Rf N)"
  by (metis Diff_subset Ri_mono Ri_subs_Ri_diff_Rf subset_antisym)

lemma Ri_subset_\<Gamma>: "Ri N \<subseteq> \<Gamma>"
  unfolding Ri_def by blast

lemma Rf_indep: "N' \<subseteq> Rf N \<Longrightarrow> Rf N \<subseteq> Rf (N - N')"
  by (metis Diff_cancel Diff_eq_empty_iff Diff_mono Rf_eq_Rf_diff_Rf Rf_mono)

lemma Ri_indep: "N' \<subseteq> Rf N \<Longrightarrow> Ri N \<subseteq> Ri (N - N')"
  by (metis Diff_mono Ri_eq_Ri_diff_Rf Ri_mono order_refl)

lemma Rf_model:
  assumes "I \<Turnstile>s N - Rf N"
  shows "I \<Turnstile>s N"
proof -
  have "I \<Turnstile>s Rf (N - Rf N)"
    unfolding true_clss_def
    by (subst Rf_def, simp add: true_cls_mset_def, metis assms subset_eq true_clss_def)
  then have "I \<Turnstile>s Rf N"
    using Rf_subs_Rf_diff_Rf true_clss_mono by blast
  then show ?thesis
    using assms by (metis Un_Diff_cancel true_clss_union)
qed

lemma Rf_sat: "satisfiable (N - Rf N) \<Longrightarrow> satisfiable N"
  by (metis Rf_model)

text \<open>
The following corresponds to Theorem 4.7:
\<close>

sublocale redundancy_criterion \<Gamma> Rf Ri
  by unfold_locales (rule Ri_subset_\<Gamma>, (elim Rf_mono Ri_mono Rf_indep Ri_indep Rf_sat)+)

end

locale standard_redundancy_criterion_reductive =
  standard_redundancy_criterion + reductive_inference_system
begin

text \<open>
The following corresponds to Theorem 4.8:
\<close>

lemma Ri_effective:
  assumes
    in_\<gamma>: "\<gamma> \<in> \<Gamma>" and
    concl_of_in_n_un_rf_n: "concl_of \<gamma> \<in> N \<union> Rf N"
  shows "\<gamma> \<in> Ri N"
proof -
  obtain CC D E where
    \<gamma>: "\<gamma> = Infer CC D E"
    by (cases \<gamma>)
  then have cc: "CC = side_prems_of \<gamma>" and d: "D = main_prem_of \<gamma>" and e: "E = concl_of \<gamma>"
    unfolding \<gamma> by simp_all
  note e_in_n_un_rf_n = concl_of_in_n_un_rf_n[folded e]

  {
    assume "E \<in> N"
    moreover have "E < D"
      using \<Gamma>_reductive e d in_\<gamma> by auto
    ultimately have
      "set_mset {#E#} \<subseteq> N" and "\<forall>I. I \<Turnstile>m {#E#} + CC \<longrightarrow> I \<Turnstile> E" and "\<forall>D'. D' \<in># {#E#} \<longrightarrow> D' < D"
      by simp_all
    then have "redundant_infer N \<gamma>"
      using cc d e by blast
  }
  moreover
  {
    assume "E \<in> Rf N"
    then obtain DD where
      dd_sset: "set_mset DD \<subseteq> N" and
      dd_imp_e: "\<forall>I. I \<Turnstile>m DD \<longrightarrow> I \<Turnstile> E" and
      dd_lt_e: "\<forall>C'. C' \<in># DD \<longrightarrow> C' < E"
      unfolding Rf_def by blast
    from dd_lt_e have "\<forall>Da. Da \<in># DD \<longrightarrow> Da < D"
      using d e in_\<gamma> \<Gamma>_reductive less_trans by blast
    then have "redundant_infer N \<gamma>"
      using dd_sset dd_imp_e cc d e by blast
  }
  ultimately show "\<gamma> \<in> Ri N"
    using in_\<gamma> e_in_n_un_rf_n unfolding Ri_def by blast
qed

sublocale effective_redundancy_criterion \<Gamma> Rf Ri
  unfolding effective_redundancy_criterion_def
  by (intro conjI redundancy_criterion_axioms, unfold_locales, rule Ri_effective)

lemma contradiction_Rf: "{#} \<in> N \<Longrightarrow> Ri N = \<Gamma>"
  unfolding Ri_def using \<Gamma>_reductive le_multiset_empty_right
  by (force intro: exI[of _ "{#{#}#}"] le_multiset_empty_left)

end

locale standard_redundancy_criterion_counterex_reducing =
  standard_redundancy_criterion + counterex_reducing_inference_system
begin

text \<open>
The following result corresponds to Theorem 4.9.
\<close>

lemma saturated_upto_complete_if:
  assumes
    satur: "saturated_upto N" and
    unsat: "\<not> satisfiable N"
  shows "{#} \<in> N"
proof (rule ccontr)
  assume ec_ni_n: "{#} \<notin> N"

  define M where
    "M = N - Rf N"

  have ec_ni_m: "{#} \<notin> M"
    unfolding M_def using ec_ni_n by fast

  have "I_of M \<Turnstile>s M"
  proof (rule ccontr)
    assume "\<not> I_of M \<Turnstile>s M"
    then obtain D where
      d_in_m: "D \<in> M" and
      d_cex: "\<not> I_of M \<Turnstile> D" and
      d_min: "\<And>C. C \<in> M \<Longrightarrow> C < D \<Longrightarrow> I_of M \<Turnstile> C"
      using ex_min_counterex by meson
    then obtain \<gamma> CC E where
      \<gamma>: "\<gamma> = Infer CC D E" and
      cc_subs_m: "set_mset CC \<subseteq> M" and
      cc_true: "I_of M \<Turnstile>m CC" and
      \<gamma>_in: "\<gamma> \<in> \<Gamma>" and
      e_cex: "\<not> I_of M \<Turnstile> E" and
      e_lt_d: "E < D"
      using \<Gamma>_counterex_reducing[OF ec_ni_m] not_less by metis
    have cc: "CC = side_prems_of \<gamma>" and d: "D = main_prem_of \<gamma>" and e: "E = concl_of \<gamma>"
      unfolding \<gamma> by simp_all
    have "\<gamma> \<in> Ri N"
      by (rule subsetD[OF satur[unfolded saturated_upto_def inferences_from_def infer_from_def]])
        (simp add: \<gamma>_in d_in_m cc_subs_m cc[symmetric] d[symmetric] M_def[symmetric])
    then have "\<gamma> \<in> Ri M"
      unfolding M_def using Ri_indep by fast
    then obtain DD where
      dd_subs_m: "set_mset DD \<subseteq> M" and
      dd_cc_imp_d: "\<forall>I. I \<Turnstile>m DD + CC \<longrightarrow> I \<Turnstile> E" and
      dd_lt_d: "\<forall>C. C \<in># DD \<longrightarrow> C < D"
      unfolding Ri_def cc d e by blast
    from dd_subs_m dd_lt_d have "I_of M \<Turnstile>m DD"
      using d_min unfolding true_cls_mset_def by (metis contra_subsetD)
    then have "I_of M \<Turnstile> E"
      using dd_cc_imp_d cc_true by auto
    then show False
      using e_cex by auto
  qed
  then have "I_of M \<Turnstile>s N"
    using M_def Rf_model by blast
  then show False
    using unsat by blast
qed

theorem saturated_upto_complete:
  assumes "saturated_upto N"
  shows "\<not> satisfiable N \<longleftrightarrow> {#} \<in> N"
  using assms saturated_upto_complete_if true_clss_def by auto

end

end
