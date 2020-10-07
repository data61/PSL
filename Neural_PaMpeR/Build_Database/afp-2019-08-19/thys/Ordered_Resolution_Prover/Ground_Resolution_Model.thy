(*  Title:       Candidate Models for Ground Resolution
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Candidate Models for Ground Resolution\<close>

theory Ground_Resolution_Model
  imports Herbrand_Interpretation
begin

text \<open>
The proofs of refutational completeness for the two resolution inference systems presented in
Section 3 (``Standard Resolution'') of Bachmair and Ganzinger's chapter share mostly the same
candidate model construction. The literal selection capability needed for the second system is
ignored by the first one, by taking @{term "\<lambda>_. {}"} as instantiation for the \<open>S\<close>
parameter.
\<close>

locale selection =
  fixes S :: "'a clause \<Rightarrow> 'a clause"
  assumes
    S_selects_subseteq: "S C \<subseteq># C" and
    S_selects_neg_lits: "L \<in># S C \<Longrightarrow> is_neg L"

locale ground_resolution_with_selection = selection S
  for S :: "('a :: wellorder) clause \<Rightarrow> 'a clause"
begin

text \<open>
The following commands corresponds to Definition 3.14, which generalizes Definition 3.1.
\<open>production C\<close> is denoted $\varepsilon_C$ in the chapter; \<open>interp C\<close> is denoted
$I_C$; \<open>Interp C\<close> is denoted $I^C$; and \<open>Interp_N\<close> is denoted $I_N$. The mutually
recursive definition from the chapter is massaged to simplify the termination argument. The
\<open>production_unfold\<close> lemma below gives the intended characterization.
\<close>

context
  fixes N :: "'a clause set"
begin

function production :: "'a clause \<Rightarrow> 'a interp" where
  "production C =
   {A. C \<in> N \<and> C \<noteq> {#} \<and> Max_mset C = Pos A \<and> \<not> (\<Union>D \<in> {D. D < C}. production D) \<Turnstile> C \<and> S C = {#}}"
  by auto
termination by (rule "termination"[OF wf, simplified])

declare production.simps [simp del]

definition interp :: "'a clause \<Rightarrow> 'a interp" where
  "interp C = (\<Union>D \<in> {D. D < C}. production D)"

lemma production_unfold:
  "production C = {A. C \<in> N \<and> C \<noteq> {#} \<and> Max_mset C = Pos A \<and> \<not> interp C \<Turnstile> C \<and> S C = {#}}"
  unfolding interp_def by (rule production.simps)

abbreviation productive :: "'a clause \<Rightarrow> bool" where
  "productive C \<equiv> production C \<noteq> {}"

abbreviation produces :: "'a clause \<Rightarrow> 'a \<Rightarrow> bool" where
  "produces C A \<equiv> production C = {A}"

lemma producesD: "produces C A \<Longrightarrow> C \<in> N \<and> C \<noteq> {#} \<and> Pos A = Max_mset C \<and> \<not> interp C \<Turnstile> C \<and> S C = {#}"
  unfolding production_unfold by auto

definition Interp :: "'a clause \<Rightarrow> 'a interp" where
  "Interp C = interp C \<union> production C"

lemma interp_subseteq_Interp[simp]: "interp C \<subseteq> Interp C"
  by (simp add: Interp_def)

lemma Interp_as_UNION: "Interp C = (\<Union>D \<in> {D. D \<le> C}. production D)"
  unfolding Interp_def interp_def less_eq_multiset_def by fast

lemma productive_not_empty: "productive C \<Longrightarrow> C \<noteq> {#}"
  unfolding production_unfold by simp

lemma productive_imp_produces_Max_literal: "productive C \<Longrightarrow> produces C (atm_of (Max_mset C))"
  unfolding production_unfold by (auto simp del: atm_of_Max_lit)

lemma productive_imp_produces_Max_atom: "productive C \<Longrightarrow> produces C (Max (atms_of C))"
  unfolding atms_of_def Max_atm_of_set_mset_commute[OF productive_not_empty]
  by (rule productive_imp_produces_Max_literal)

lemma produces_imp_Max_literal: "produces C A \<Longrightarrow> A = atm_of (Max_mset C)"
  using productive_imp_produces_Max_literal by auto

lemma produces_imp_Max_atom: "produces C A \<Longrightarrow> A = Max (atms_of C)"
  using producesD produces_imp_Max_literal by auto

lemma produces_imp_Pos_in_lits: "produces C A \<Longrightarrow> Pos A \<in># C"
  by (simp add: producesD)

lemma productive_in_N: "productive C \<Longrightarrow> C \<in> N"
  unfolding production_unfold by simp

lemma produces_imp_atms_leq: "produces C A \<Longrightarrow> B \<in> atms_of C \<Longrightarrow> B \<le> A"
  using Max.coboundedI produces_imp_Max_atom by blast

lemma produces_imp_neg_notin_lits: "produces C A \<Longrightarrow> \<not> Neg A \<in># C"
  by (simp add: pos_Max_imp_neg_notin producesD)

lemma less_eq_imp_interp_subseteq_interp: "C \<le> D \<Longrightarrow> interp C \<subseteq> interp D"
  unfolding interp_def by auto (metis order.strict_trans2)

lemma less_eq_imp_interp_subseteq_Interp: "C \<le> D \<Longrightarrow> interp C \<subseteq> Interp D"
  unfolding Interp_def using less_eq_imp_interp_subseteq_interp by blast

lemma less_imp_production_subseteq_interp: "C < D \<Longrightarrow> production C \<subseteq> interp D"
  unfolding interp_def by fast

lemma less_eq_imp_production_subseteq_Interp: "C \<le> D \<Longrightarrow> production C \<subseteq> Interp D"
  unfolding Interp_def using less_imp_production_subseteq_interp
  by (metis le_imp_less_or_eq le_supI1 sup_ge2)

lemma less_imp_Interp_subseteq_interp: "C < D \<Longrightarrow> Interp C \<subseteq> interp D"
  by (simp add: Interp_def less_eq_imp_interp_subseteq_interp less_imp_production_subseteq_interp)

lemma less_eq_imp_Interp_subseteq_Interp: "C \<le> D \<Longrightarrow> Interp C \<subseteq> Interp D"
  using Interp_def less_eq_imp_interp_subseteq_Interp less_eq_imp_production_subseteq_Interp by auto

lemma not_Interp_to_interp_imp_less: "A \<notin> Interp C \<Longrightarrow> A \<in> interp D \<Longrightarrow> C < D"
  using less_eq_imp_interp_subseteq_Interp not_less by blast

lemma not_interp_to_interp_imp_less: "A \<notin> interp C \<Longrightarrow> A \<in> interp D \<Longrightarrow> C < D"
  using less_eq_imp_interp_subseteq_interp not_less by blast

lemma not_Interp_to_Interp_imp_less: "A \<notin> Interp C \<Longrightarrow> A \<in> Interp D \<Longrightarrow> C < D"
  using less_eq_imp_Interp_subseteq_Interp not_less by blast

lemma not_interp_to_Interp_imp_le: "A \<notin> interp C \<Longrightarrow> A \<in> Interp D \<Longrightarrow> C \<le> D"
  using less_imp_Interp_subseteq_interp not_less by blast

definition INTERP :: "'a interp" where
  "INTERP = (\<Union>C \<in> N. production C)"

lemma interp_subseteq_INTERP: "interp C \<subseteq> INTERP"
  unfolding interp_def INTERP_def by (auto simp: production_unfold)

lemma production_subseteq_INTERP: "production C \<subseteq> INTERP"
  unfolding INTERP_def using production_unfold by blast

lemma Interp_subseteq_INTERP: "Interp C \<subseteq> INTERP"
  by (simp add: Interp_def interp_subseteq_INTERP production_subseteq_INTERP)

lemma produces_imp_in_interp:
  assumes a_in_c: "Neg A \<in># C" and d: "produces D A"
  shows "A \<in> interp C"
  by (metis Interp_def Max_pos_neg_less_multiset UnCI a_in_c d
      not_interp_to_Interp_imp_le not_less producesD singletonI)

lemma neg_notin_Interp_not_produce: "Neg A \<in># C \<Longrightarrow> A \<notin> Interp D \<Longrightarrow> C \<le> D \<Longrightarrow> \<not> produces D'' A"
  using less_eq_imp_interp_subseteq_Interp produces_imp_in_interp by blast

lemma in_production_imp_produces: "A \<in> production C \<Longrightarrow> produces C A"
  using productive_imp_produces_Max_atom by fastforce

lemma not_produces_imp_notin_production: "\<not> produces C A \<Longrightarrow> A \<notin> production C"
  using in_production_imp_produces by blast

lemma not_produces_imp_notin_interp: "(\<And>D. \<not> produces D A) \<Longrightarrow> A \<notin> interp C"
  unfolding interp_def by (fast intro!: in_production_imp_produces)

text \<open>
The results below corresponds to Lemma 3.4.
\<close>

lemma Interp_imp_general:
  assumes
    c_le_d: "C \<le> D" and
    d_lt_d': "D < D'" and
    c_at_d: "Interp D \<Turnstile> C" and
    subs: "interp D' \<subseteq> (\<Union>C \<in> CC. production C)"
  shows "(\<Union>C \<in> CC. production C) \<Turnstile> C"
proof (cases "\<exists>A. Pos A \<in># C \<and> A \<in> Interp D")
  case True
  then obtain A where a_in_c: "Pos A \<in># C" and a_at_d: "A \<in> Interp D"
    by blast
  from a_at_d have "A \<in> interp D'"
    using d_lt_d' less_imp_Interp_subseteq_interp by blast
  then show ?thesis
    using subs a_in_c by (blast dest: contra_subsetD)
next
  case False
  then obtain A where a_in_c: "Neg A \<in># C" and "A \<notin> Interp D"
    using c_at_d unfolding true_cls_def by blast
  then have "\<And>D''. \<not> produces D'' A"
    using c_le_d neg_notin_Interp_not_produce by simp
  then show ?thesis
    using a_in_c subs not_produces_imp_notin_production by auto
qed

lemma Interp_imp_interp: "C \<le> D \<Longrightarrow> D < D' \<Longrightarrow> Interp D \<Turnstile> C \<Longrightarrow> interp D' \<Turnstile> C"
  using interp_def Interp_imp_general by simp

lemma Interp_imp_Interp: "C \<le> D \<Longrightarrow> D \<le> D' \<Longrightarrow> Interp D \<Turnstile> C \<Longrightarrow> Interp D' \<Turnstile> C"
  using Interp_as_UNION interp_subseteq_Interp Interp_imp_general by (metis antisym_conv2)

lemma Interp_imp_INTERP: "C \<le> D \<Longrightarrow> Interp D \<Turnstile> C \<Longrightarrow> INTERP \<Turnstile> C"
  using INTERP_def interp_subseteq_INTERP Interp_imp_general[OF _ le_multiset_right_total] by simp

lemma interp_imp_general:
  assumes
    c_le_d: "C \<le> D" and
    d_le_d': "D \<le> D'" and
    c_at_d: "interp D \<Turnstile> C" and
    subs: "interp D' \<subseteq> (\<Union>C \<in> CC. production C)"
  shows "(\<Union>C \<in> CC. production C) \<Turnstile> C"
proof (cases "\<exists>A. Pos A \<in># C \<and> A \<in> interp D")
  case True
  then obtain A where a_in_c: "Pos A \<in># C" and a_at_d: "A \<in> interp D"
    by blast
  from a_at_d have "A \<in> interp D'"
    using d_le_d' less_eq_imp_interp_subseteq_interp by blast
  then show ?thesis
    using subs a_in_c by (blast dest: contra_subsetD)
next
  case False
  then obtain A where a_in_c: "Neg A \<in># C" and "A \<notin> interp D"
    using c_at_d unfolding true_cls_def by blast
  then have "\<And>D''. \<not> produces D'' A"
    using c_le_d by (auto dest: produces_imp_in_interp less_eq_imp_interp_subseteq_interp)
  then show ?thesis
    using a_in_c subs not_produces_imp_notin_production by auto
qed

lemma interp_imp_interp: "C \<le> D \<Longrightarrow> D \<le> D' \<Longrightarrow> interp D \<Turnstile> C \<Longrightarrow> interp D' \<Turnstile> C"
  using interp_def interp_imp_general by simp

lemma interp_imp_Interp: "C \<le> D \<Longrightarrow> D \<le> D' \<Longrightarrow> interp D \<Turnstile> C \<Longrightarrow> Interp D' \<Turnstile> C"
  using Interp_as_UNION interp_subseteq_Interp[of D'] interp_imp_general by simp

lemma interp_imp_INTERP: "C \<le> D \<Longrightarrow> interp D \<Turnstile> C \<Longrightarrow> INTERP \<Turnstile> C"
  using INTERP_def interp_subseteq_INTERP interp_imp_general linear by metis

lemma productive_imp_not_interp: "productive C \<Longrightarrow> \<not> interp C \<Turnstile> C"
  unfolding production_unfold by simp

text \<open>
This corresponds to Lemma 3.3:
\<close>

lemma productive_imp_Interp:
  assumes "productive C"
  shows "Interp C \<Turnstile> C"
proof -
  obtain A where a: "produces C A"
    using assms productive_imp_produces_Max_atom by blast
  then have a_in_c: "Pos A \<in># C"
    by (rule produces_imp_Pos_in_lits)
  moreover have "A \<in> Interp C"
    using a less_eq_imp_production_subseteq_Interp by blast
  ultimately show ?thesis
    by fast
qed

lemma productive_imp_INTERP: "productive C \<Longrightarrow> INTERP \<Turnstile> C"
  by (fast intro: productive_imp_Interp Interp_imp_INTERP)

text \<open>
This corresponds to Lemma 3.5:
\<close>

lemma max_pos_imp_Interp:
  assumes "C \<in> N" and "C \<noteq> {#}" and "Max_mset C = Pos A" and "S C = {#}"
  shows "Interp C \<Turnstile> C"
proof (cases "productive C")
  case True
  then show ?thesis
    by (fast intro: productive_imp_Interp)
next
  case False
  then have "interp C \<Turnstile> C"
    using assms unfolding production_unfold by simp
  then show ?thesis
    unfolding Interp_def using False by auto
qed

text \<open>
The following results correspond to Lemma 3.6:
\<close>

lemma max_atm_imp_Interp:
  assumes
    c_in_n: "C \<in> N" and
    pos_in: "Pos A \<in># C" and
    max_atm: "A = Max (atms_of C)" and
    s_c_e: "S C = {#}"
  shows "Interp C \<Turnstile> C"
proof (cases "Neg A \<in># C")
  case True
  then show ?thesis
    using pos_in pos_neg_in_imp_true by metis
next
  case False
  moreover have ne: "C \<noteq> {#}"
    using pos_in by auto
  ultimately have "Max_mset C = Pos A"
    using max_atm using Max_in_lits Max_lit_eq_pos_or_neg_Max_atm by metis
  then show ?thesis
    using ne c_in_n s_c_e by (blast intro: max_pos_imp_Interp)
qed

lemma not_Interp_imp_general:
  assumes
    d'_le_d: "D' \<le> D" and
    in_n_or_max_gt: "D' \<in> N \<and> S D' = {#} \<or> Max (atms_of D') < Max (atms_of D)" and
    d'_at_d: "\<not> Interp D \<Turnstile> D'" and
    d_lt_c: "D < C" and
    subs: "interp C \<subseteq> (\<Union>C \<in> CC. production C)"
  shows "\<not> (\<Union>C \<in> CC. production C) \<Turnstile> D'"
proof -
  {
    assume cc_blw_d': "(\<Union>C \<in> CC. production C) \<Turnstile> D'"
    have "Interp D \<subseteq> (\<Union>C \<in> CC. production C)"
      using less_imp_Interp_subseteq_interp d_lt_c subs by blast
    then obtain A where a_in_d': "Pos A \<in># D'" and a_blw_cc: "A \<in> (\<Union>C \<in> CC. production C)"
      using cc_blw_d' d'_at_d false_to_true_imp_ex_pos by metis
    from a_in_d' have a_at_d: "A \<notin> Interp D"
      using d'_at_d by fast
    from a_blw_cc obtain C' where prod_c': "production C' = {A}"
      by (fast intro!: in_production_imp_produces)
    have max_c': "Max (atms_of C') = A"
      using prod_c' productive_imp_produces_Max_atom by force
    have leq_dc': "D \<le> C'"
      using a_at_d d'_at_d prod_c' by (auto simp: Interp_def intro: not_interp_to_Interp_imp_le)
    then have "D' \<le> C'"
      using d'_le_d order_trans by blast
    then have max_d': "Max (atms_of D') = A"
      using a_in_d' max_c' by (fast intro: pos_lit_in_atms_of le_multiset_Max_in_imp_Max)

    {
      assume "D' \<in> N \<and> S D' = {#}"
      then have "Interp D' \<Turnstile> D'"
        using a_in_d' max_d' by (blast intro: max_atm_imp_Interp)
      then have "Interp D \<Turnstile> D'"
        using d'_le_d by (auto intro: Interp_imp_Interp simp: less_eq_multiset_def)
      then have False
        using d'_at_d by satx
    }
    moreover
    {
      assume "Max (atms_of D') < Max (atms_of D)"
      then have False
        using max_d' leq_dc' max_c' d'_le_d
        by (metis le_imp_less_or_eq le_multiset_empty_right less_eq_Max_atms_of less_imp_not_less)
    }
    ultimately have False
      using in_n_or_max_gt by satx
  }
  then show ?thesis
    by satx
qed

lemma not_Interp_imp_not_interp:
  "D' \<le> D \<Longrightarrow> D' \<in> N \<and> S D' = {#} \<or> Max (atms_of D') < Max (atms_of D) \<Longrightarrow> \<not> Interp D \<Turnstile> D' \<Longrightarrow>
   D < C \<Longrightarrow> \<not> interp C \<Turnstile> D'"
  using interp_def not_Interp_imp_general by simp

lemma not_Interp_imp_not_Interp:
  "D' \<le> D \<Longrightarrow> D' \<in> N \<and> S D' = {#} \<or> Max (atms_of D') < Max (atms_of D) \<Longrightarrow> \<not> Interp D \<Turnstile> D' \<Longrightarrow>
   D < C \<Longrightarrow> \<not> Interp C \<Turnstile> D'"
  using Interp_as_UNION interp_subseteq_Interp not_Interp_imp_general by metis

lemma not_Interp_imp_not_INTERP:
  "D' \<le> D \<Longrightarrow> D' \<in> N \<and> S D' = {#} \<or> Max (atms_of D') < Max (atms_of D) \<Longrightarrow> \<not> Interp D \<Turnstile> D' \<Longrightarrow>
   \<not> INTERP \<Turnstile> D'"
  using INTERP_def interp_subseteq_INTERP not_Interp_imp_general[OF _ _ _ le_multiset_right_total]
  by simp

text \<open>
Lemma 3.7 is a problem child. It is stated below but not proved; instead, a counterexample is
displayed. This is not much of a problem, because it is not invoked in the rest of the chapter.
\<close>

lemma
  assumes "D \<in> N" and "\<And>D'. D' < D \<Longrightarrow> Interp D' \<Turnstile> C"
  shows "interp D \<Turnstile> C"
  oops

lemma
  assumes d: "D = {#}" and n: "N = {D, C}" and c: "C = {#Pos A#}"
  shows "D \<in> N" and "\<And>D'. D' < D \<Longrightarrow> Interp D' \<Turnstile> C" and "\<not> interp D \<Turnstile> C"
  using n unfolding d c interp_def by auto

end

end

end
