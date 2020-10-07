(*  Title:       Theorem Proving Processes
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Theorem Proving Processes\<close>

theory Proving_Process
  imports Unordered_Ground_Resolution Lazy_List_Chain
begin

text \<open>
This material corresponds to Section 4.1 (``Theorem Proving Processes'') of Bachmair and Ganzinger's
chapter.

The locale assumptions below capture conditions R1 to R3 of Definition 4.1.
\<open>Rf\<close> denotes $\mathcal{R}_{\mathcal{F}}$; \<open>Ri\<close> denotes $\mathcal{R}_{\mathcal{I}}$.
\<close>

locale redundancy_criterion = inference_system +
  fixes
    Rf :: "'a clause set \<Rightarrow> 'a clause set" and
    Ri :: "'a clause set \<Rightarrow> 'a inference set"
  assumes
    Ri_subset_\<Gamma>: "Ri N \<subseteq> \<Gamma>" and
    Rf_mono: "N \<subseteq> N' \<Longrightarrow> Rf N \<subseteq> Rf N'" and
    Ri_mono: "N \<subseteq> N' \<Longrightarrow> Ri N \<subseteq> Ri N'" and
    Rf_indep: "N' \<subseteq> Rf N \<Longrightarrow> Rf N \<subseteq> Rf (N - N')" and
    Ri_indep: "N' \<subseteq> Rf N \<Longrightarrow> Ri N \<subseteq> Ri (N - N')" and
    Rf_sat: "satisfiable (N - Rf N) \<Longrightarrow> satisfiable N"
begin

definition saturated_upto :: "'a clause set \<Rightarrow> bool" where
  "saturated_upto N \<longleftrightarrow> inferences_from (N - Rf N) \<subseteq> Ri N"

inductive "derive" :: "'a clause set \<Rightarrow> 'a clause set \<Rightarrow> bool" (infix "\<triangleright>" 50) where
  deduction_deletion: "N - M \<subseteq> concls_of (inferences_from M) \<Longrightarrow> M - N \<subseteq> Rf N \<Longrightarrow> M \<triangleright> N"

lemma derive_subset: "M \<triangleright> N \<Longrightarrow> N \<subseteq> M \<union> concls_of (inferences_from M)"
  by (meson Diff_subset_conv derive.cases)

end

locale sat_preserving_redundancy_criterion =
  sat_preserving_inference_system "\<Gamma> :: ('a :: wellorder) inference set" + redundancy_criterion
begin

lemma deriv_sat_preserving:
  assumes
    deriv: "chain (\<triangleright>) Ns" and
    sat_n0: "satisfiable (lhd Ns)"
  shows "satisfiable (Sup_llist Ns)"
proof -
  have ns0: "lnth Ns 0 = lhd Ns"
    using deriv by (metis chain_not_lnull lhd_conv_lnth)
  have len_ns: "llength Ns > 0"
    using deriv by (case_tac Ns) simp+
  {
    fix DD
    assume fin: "finite DD" and sset_lun: "DD \<subseteq> Sup_llist Ns"
    then obtain k where dd_sset: "DD \<subseteq> Sup_upto_llist Ns k"
      using finite_Sup_llist_imp_Sup_upto_llist by blast
    have "satisfiable (Sup_upto_llist Ns k)"
    proof (induct k)
      case 0
      then show ?case
        using len_ns ns0 sat_n0 unfolding Sup_upto_llist_def true_clss_def by auto
    next
      case (Suc k)
      show ?case
      proof (cases "enat (Suc k) \<ge> llength Ns")
        case True
        then have "Sup_upto_llist Ns k = Sup_upto_llist Ns (Suc k)"
          unfolding Sup_upto_llist_def using le_Suc_eq not_less by blast
        then show ?thesis
          using Suc by simp
      next
        case False
        then have "lnth Ns k \<triangleright> lnth Ns (Suc k)"
          using deriv by (auto simp: chain_lnth_rel)
        then have "lnth Ns (Suc k) \<subseteq> lnth Ns k \<union> concls_of (inferences_from (lnth Ns k))"
          by (rule derive_subset)
        moreover have "lnth Ns k \<subseteq> Sup_upto_llist Ns k"
          unfolding Sup_upto_llist_def using False Suc_ile_eq linear by blast
        ultimately have "lnth Ns (Suc k)
          \<subseteq> Sup_upto_llist Ns k \<union> concls_of (inferences_from (Sup_upto_llist Ns k))"
          by clarsimp (metis UnCI UnE image_Un inferences_from_mono le_iff_sup)
        moreover have "Sup_upto_llist Ns (Suc k) = Sup_upto_llist Ns k \<union> lnth Ns (Suc k)"
          unfolding Sup_upto_llist_def using False by (force elim: le_SucE)
        moreover have
          "satisfiable (Sup_upto_llist Ns k \<union> concls_of (inferences_from (Sup_upto_llist Ns k)))"
          using Suc \<Gamma>_sat_preserving unfolding sat_preserving_inference_system_def by simp
        ultimately show ?thesis
          by (metis le_iff_sup true_clss_union)
      qed
    qed
    then have "satisfiable DD"
      using dd_sset unfolding Sup_upto_llist_def by (blast intro: true_clss_mono)
  }
  then show ?thesis
    using ground_resolution_without_selection.clausal_logic_compact[THEN iffD1] by metis
qed

text \<open>
This corresponds to Lemma 4.2:
\<close>

lemma
  assumes deriv: "chain (\<triangleright>) Ns"
  shows
    Rf_Sup_subset_Rf_Liminf: "Rf (Sup_llist Ns) \<subseteq> Rf (Liminf_llist Ns)" and
    Ri_Sup_subset_Ri_Liminf: "Ri (Sup_llist Ns) \<subseteq> Ri (Liminf_llist Ns)" and
    sat_limit_iff: "satisfiable (Liminf_llist Ns) \<longleftrightarrow> satisfiable (lhd Ns)"
proof -
  {
    fix C i j
    assume
      c_in: "C \<in> lnth Ns i" and
      c_ni: "C \<notin> Rf (Sup_llist Ns)" and
      j: "j \<ge> i" and
      j': "enat j < llength Ns"
    from c_ni have c_ni': "\<And>i. enat i < llength Ns \<Longrightarrow> C \<notin> Rf (lnth Ns i)"
      using Rf_mono lnth_subset_Sup_llist Sup_llist_def by (blast dest: contra_subsetD)
    have "C \<in> lnth Ns j"
    using j j'
    proof (induct j)
      case 0
      then show ?case
        using c_in by blast
    next
      case (Suc k)
      then show ?case
      proof (cases "i < Suc k")
        case True
        have "i \<le> k"
          using True by linarith
        moreover have "enat k < llength Ns"
          using Suc.prems(2) Suc_ile_eq by (blast intro: dual_order.strict_implies_order)
        ultimately have c_in_k: "C \<in> lnth Ns k"
          using Suc.hyps by blast
        have rel: "lnth Ns k \<triangleright> lnth Ns (Suc k)"
          using Suc.prems deriv by (auto simp: chain_lnth_rel)
        then show ?thesis
          using c_in_k c_ni' Suc.prems(2) by cases auto
      next
        case False
        then show ?thesis
          using Suc c_in by auto
      qed
    qed
  }
  then have lu_ll: "Sup_llist Ns - Rf (Sup_llist Ns) \<subseteq> Liminf_llist Ns"
    unfolding Sup_llist_def Liminf_llist_def by blast
  have rf: "Rf (Sup_llist Ns - Rf (Sup_llist Ns)) \<subseteq> Rf (Liminf_llist Ns)"
    using lu_ll Rf_mono by simp
  have ri: "Ri (Sup_llist Ns - Rf (Sup_llist Ns)) \<subseteq> Ri (Liminf_llist Ns)"
    using lu_ll Ri_mono by simp
  show "Rf (Sup_llist Ns) \<subseteq> Rf (Liminf_llist Ns)"
    using rf Rf_indep by blast
  show "Ri (Sup_llist Ns) \<subseteq> Ri (Liminf_llist Ns)"
    using ri Ri_indep by blast

  show "satisfiable (Liminf_llist Ns) \<longleftrightarrow> satisfiable (lhd Ns)"
  proof
    assume "satisfiable (lhd Ns)"
    then have "satisfiable (Sup_llist Ns)"
      using deriv deriv_sat_preserving by simp
    then show "satisfiable (Liminf_llist Ns)"
      using true_clss_mono[OF Liminf_llist_subset_Sup_llist] by blast
  next
    assume "satisfiable (Liminf_llist Ns)"
    then have "satisfiable (Sup_llist Ns - Rf (Sup_llist Ns))"
      using true_clss_mono[OF lu_ll] by blast
    then have "satisfiable (Sup_llist Ns)"
      using Rf_sat by blast
    then show "satisfiable (lhd Ns)"
      using deriv true_clss_mono lhd_subset_Sup_llist chain_not_lnull by metis
  qed
qed

lemma
  assumes "chain (\<triangleright>) Ns"
  shows
    Rf_limit_Sup: "Rf (Liminf_llist Ns) = Rf (Sup_llist Ns)" and
    Ri_limit_Sup: "Ri (Liminf_llist Ns) = Ri (Sup_llist Ns)"
  using assms
  by (auto simp: Rf_Sup_subset_Rf_Liminf Rf_mono Ri_Sup_subset_Ri_Liminf Ri_mono
      Liminf_llist_subset_Sup_llist subset_antisym)

end

text \<open>
The assumption below corresponds to condition R4 of Definition 4.1.
\<close>

locale effective_redundancy_criterion = redundancy_criterion +
  assumes Ri_effective: "\<gamma> \<in> \<Gamma> \<Longrightarrow> concl_of \<gamma> \<in> N \<union> Rf N \<Longrightarrow> \<gamma> \<in> Ri N"
begin

definition fair_clss_seq :: "'a clause set llist \<Rightarrow> bool" where
  "fair_clss_seq Ns \<longleftrightarrow> (let N' = Liminf_llist Ns - Rf (Liminf_llist Ns) in
     concls_of (inferences_from N' - Ri N') \<subseteq> Sup_llist Ns \<union> Rf (Sup_llist Ns))"

end

locale sat_preserving_effective_redundancy_criterion =
  sat_preserving_inference_system "\<Gamma> :: ('a :: wellorder) inference set" +
  effective_redundancy_criterion
begin

sublocale sat_preserving_redundancy_criterion
  ..

text \<open>
The result below corresponds to Theorem 4.3.
\<close>

theorem fair_derive_saturated_upto:
  assumes
    deriv: "chain (\<triangleright>) Ns" and
    fair: "fair_clss_seq Ns"
  shows "saturated_upto (Liminf_llist Ns)"
  unfolding saturated_upto_def
proof
  fix \<gamma>
  let ?N' = "Liminf_llist Ns - Rf (Liminf_llist Ns)"
  assume \<gamma>: "\<gamma> \<in> inferences_from ?N'"
  show "\<gamma> \<in> Ri (Liminf_llist Ns)"
  proof (cases "\<gamma> \<in> Ri ?N'")
    case True
    then show ?thesis
      using Ri_mono by blast
  next
    case False
    have "concls_of (inferences_from ?N' - Ri ?N') \<subseteq> Sup_llist Ns \<union> Rf (Sup_llist Ns)"
      using fair unfolding fair_clss_seq_def Let_def .
    then have "concl_of \<gamma> \<in> Sup_llist Ns \<union> Rf (Sup_llist Ns)"
      using False \<gamma> by auto
    moreover
    {
      assume "concl_of \<gamma> \<in> Sup_llist Ns"
      then have "\<gamma> \<in> Ri (Sup_llist Ns)"
        using \<gamma> Ri_effective inferences_from_def by blast
      then have "\<gamma> \<in> Ri (Liminf_llist Ns)"
        using deriv Ri_Sup_subset_Ri_Liminf by fast
    }
    moreover
    {
      assume "concl_of \<gamma> \<in> Rf (Sup_llist Ns)"
      then have "concl_of \<gamma> \<in> Rf (Liminf_llist Ns)"
        using deriv Rf_Sup_subset_Rf_Liminf by blast
      then have "\<gamma> \<in> Ri (Liminf_llist Ns)"
        using \<gamma> Ri_effective inferences_from_def by auto
    }
    ultimately show "\<gamma> \<in> Ri (Liminf_llist Ns)"
      by blast
  qed
qed

end

text \<open>
This corresponds to the trivial redundancy criterion defined on page 36 of
Section 4.1.
\<close>

locale trivial_redundancy_criterion = inference_system
begin

definition Rf :: "'a clause set \<Rightarrow> 'a clause set" where
  "Rf _ = {}"

definition Ri :: "'a clause set \<Rightarrow> 'a inference set" where
  "Ri N = {\<gamma>. \<gamma> \<in> \<Gamma> \<and> concl_of \<gamma> \<in> N}"

sublocale effective_redundancy_criterion \<Gamma> Rf Ri
  by unfold_locales (auto simp: Rf_def Ri_def)

lemma saturated_upto_iff: "saturated_upto N \<longleftrightarrow> concls_of (inferences_from N) \<subseteq> N"
  unfolding saturated_upto_def inferences_from_def Rf_def Ri_def by auto

end

text \<open>
The following lemmas corresponds to the standard extension of a redundancy criterion defined on
page 38 of Section 4.1.
\<close>

lemma redundancy_criterion_standard_extension:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "redundancy_criterion \<Gamma> Rf Ri"
  shows "redundancy_criterion \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))"
  using assms unfolding redundancy_criterion_def by (intro conjI) ((auto simp: rev_subsetD)[5], sat)

lemma redundancy_criterion_standard_extension_saturated_upto_iff:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "redundancy_criterion \<Gamma> Rf Ri"
  shows "redundancy_criterion.saturated_upto \<Gamma> Rf Ri M \<longleftrightarrow>
    redundancy_criterion.saturated_upto \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) M"
  using assms redundancy_criterion.saturated_upto_def redundancy_criterion.saturated_upto_def
    redundancy_criterion_standard_extension
  unfolding inference_system.inferences_from_def by blast

lemma redundancy_criterion_standard_extension_effective:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "effective_redundancy_criterion \<Gamma> Rf Ri"
  shows "effective_redundancy_criterion \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))"
  using assms redundancy_criterion_standard_extension[of \<Gamma>]
  unfolding effective_redundancy_criterion_def effective_redundancy_criterion_axioms_def by auto

lemma redundancy_criterion_standard_extension_fair_iff:
  assumes "\<Gamma> \<subseteq> \<Gamma>'" and "effective_redundancy_criterion \<Gamma> Rf Ri"
  shows "effective_redundancy_criterion.fair_clss_seq \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) Ns \<longleftrightarrow>
    effective_redundancy_criterion.fair_clss_seq \<Gamma> Rf Ri Ns"
  using assms redundancy_criterion_standard_extension_effective[of \<Gamma> \<Gamma>' Rf Ri]
    effective_redundancy_criterion.fair_clss_seq_def[of \<Gamma> Rf Ri Ns]
    effective_redundancy_criterion.fair_clss_seq_def[of \<Gamma>' Rf "(\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))" Ns]
  unfolding inference_system.inferences_from_def Let_def by auto

theorem redundancy_criterion_standard_extension_fair_derive_saturated_upto:
  assumes
    subs: "\<Gamma> \<subseteq> \<Gamma>'" and
    red: "redundancy_criterion \<Gamma> Rf Ri" and
    red': "sat_preserving_effective_redundancy_criterion \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>))" and
    deriv: "chain (redundancy_criterion.derive \<Gamma>' Rf) Ns" and
    fair: "effective_redundancy_criterion.fair_clss_seq \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) Ns"
  shows "redundancy_criterion.saturated_upto \<Gamma> Rf Ri (Liminf_llist Ns)"
proof -
  have "redundancy_criterion.saturated_upto \<Gamma>' Rf (\<lambda>N. Ri N \<union> (\<Gamma>' - \<Gamma>)) (Liminf_llist Ns)"
    by (rule sat_preserving_effective_redundancy_criterion.fair_derive_saturated_upto
        [OF red' deriv fair])
  then show ?thesis
    by (rule redundancy_criterion_standard_extension_saturated_upto_iff[THEN iffD2, OF subs red])
qed

end
