(*  Title:       Ground Unordered Resolution Calculus
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Ground Unordered Resolution Calculus\<close>

theory Unordered_Ground_Resolution
  imports Inference_System Ground_Resolution_Model
begin

text \<open>
Unordered ground resolution is one of the two inference systems studied in Section 3 (``Standard
Resolution'') of Bachmair and Ganzinger's chapter.
\<close>


subsection \<open>Inference Rule\<close>

text \<open>
Unordered ground resolution consists of a single rule, called \<open>unord_resolve\<close> below, which is
sound and counterexample-reducing.
\<close>

locale ground_resolution_without_selection
begin

sublocale ground_resolution_with_selection where S = "\<lambda>_. {#}"
  by unfold_locales auto

inductive unord_resolve :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "unord_resolve (C + replicate_mset (Suc n) (Pos A)) (add_mset (Neg A) D) (C + D)"

lemma unord_resolve_sound: "unord_resolve C D E \<Longrightarrow> I \<Turnstile> C \<Longrightarrow> I \<Turnstile> D \<Longrightarrow> I \<Turnstile> E"
  using unord_resolve.cases by fastforce

text \<open>
The following result corresponds to Theorem 3.8, except that the conclusion is strengthened slightly
to make it fit better with the counterexample-reducing inference system framework.
\<close>

theorem unord_resolve_counterex_reducing:
  assumes
    ec_ni_n: "{#} \<notin> N" and
    c_in_n: "C \<in> N" and
    c_cex: "\<not> INTERP N \<Turnstile> C" and
    c_min: "\<And>D. D \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> D \<Longrightarrow> C \<le> D"
  obtains D E where
    "D \<in> N"
    "INTERP N \<Turnstile> D"
    "productive N D"
    "unord_resolve D C E"
    "\<not> INTERP N \<Turnstile> E"
    "E < C"
proof -
  have c_ne: "C \<noteq> {#}"
    using c_in_n ec_ni_n by blast
  have "\<exists>A. A \<in> atms_of C \<and> A = Max (atms_of C)"
    using c_ne by (blast intro: Max_in_lits atm_of_Max_lit atm_of_lit_in_atms_of)
  then have "\<exists>A. Neg A \<in># C"
    using c_ne c_in_n c_cex c_min Max_in_lits Max_lit_eq_pos_or_neg_Max_atm  max_pos_imp_Interp
      Interp_imp_INTERP by metis
  then obtain A where neg_a_in_c: "Neg A \<in># C"
    by blast
  then obtain C' where c: "C = add_mset (Neg A) C'"
    using insert_DiffM by metis
  have "A \<in> INTERP N"
    using neg_a_in_c c_cex[unfolded true_cls_def] by fast
  then obtain D where d0: "produces N D A"
    unfolding INTERP_def by (metis UN_E not_produces_imp_notin_production)
  have prod_d: "productive N D"
    unfolding d0 by simp
  then have d_in_n: "D \<in> N"
    using productive_in_N by fast
  have d_true: "INTERP N \<Turnstile> D"
    using prod_d productive_imp_INTERP by blast

  obtain D' AAA where
    d: "D = D' + AAA" and
    d': "D' = {#L \<in># D. L \<noteq> Pos A#}" and
    aa: "AAA = {#L \<in># D. L = Pos A#}"
    using multiset_partition union_commute by metis
  have d'_subs: "set_mset D' \<subseteq> set_mset D"
    unfolding d' by auto
  have "\<not> Neg A \<in># D"
    using d0 by (blast dest: produces_imp_neg_notin_lits)
  then have neg_a_ni_d': "\<not> Neg A \<in># D'"
    using d'_subs by auto
  have a_ni_d': "A \<notin> atms_of D'"
    using d' neg_a_ni_d' by (auto dest: atm_imp_pos_or_neg_lit)
  have "\<exists>n. AAA = replicate_mset (Suc n) (Pos A)"
    using aa d0 not0_implies_Suc produces_imp_Pos_in_lits[of N]
    by (simp add: filter_eq_replicate_mset del: replicate_mset_Suc)
  then have res_e: "unord_resolve D C (D' + C')"
    unfolding c d by (fastforce intro: unord_resolve.intros)

  have d'_le_d: "D' \<le> D"
    unfolding d by simp
  have a_max_d: "A = Max (atms_of D)"
    using d0 productive_imp_produces_Max_atom by auto
  then have "D' \<noteq> {#} \<Longrightarrow> Max (atms_of D') \<le> A"
    using d'_le_d by (blast intro: less_eq_Max_atms_of)
  moreover have "D' \<noteq> {#} \<Longrightarrow> Max (atms_of D') \<noteq> A"
    using a_ni_d' Max_in by (blast intro: atms_empty_iff_empty[THEN iffD1])
  ultimately have max_d'_lt_a: "D' \<noteq> {#} \<Longrightarrow> Max (atms_of D') < A"
    using dual_order.strict_iff_order by blast

  have "\<not> interp N D \<Turnstile> D"
    using d0 productive_imp_not_interp by blast
  then have "\<not> Interp N D \<Turnstile> D'"
    unfolding d0 d' Interp_def true_cls_def by (auto simp: true_lit_def simp del: not_gr_zero)
  then have "\<not> INTERP N \<Turnstile> D'"
    using a_max_d d'_le_d max_d'_lt_a not_Interp_imp_not_INTERP by blast
  moreover have "\<not> INTERP N \<Turnstile> C'"
    using c_cex unfolding c by simp
  ultimately have e_cex: "\<not> INTERP N \<Turnstile> D' + C'"
    by simp

  have "\<And>B. B \<in> atms_of D' \<Longrightarrow> B \<le> A"
    using d0 d'_subs contra_subsetD lits_subseteq_imp_atms_subseteq produces_imp_atms_leq by metis
  then have "\<And>L. L \<in># D' \<Longrightarrow> L < Neg A"
    using neg_a_ni_d' antisym_conv1 atms_less_eq_imp_lit_less_eq_neg by metis
  then have lt_cex: "D' + C' < C"
    by (force intro: add.commute simp: c less_multiset\<^sub>D\<^sub>M intro: exI[of _ "{#Neg A#}"])

  from d_in_n d_true prod_d res_e e_cex lt_cex show ?thesis ..
qed


subsection \<open>Inference System\<close>

text \<open>
Theorem 3.9 and Corollary 3.10 are subsumed in the counterexample-reducing inference system
framework, which is instantiated below.
\<close>

definition unord_\<Gamma> :: "'a inference set" where
  "unord_\<Gamma> = {Infer {#C#} D E | C D E. unord_resolve C D E}"

sublocale unord_\<Gamma>_sound_counterex_reducing?:
  sound_counterex_reducing_inference_system unord_\<Gamma> INTERP
proof unfold_locales
  fix D E and N :: "('b :: wellorder) clause set"
  assume "{#} \<notin> N" and "D \<in> N" and "\<not> INTERP N \<Turnstile> D" and "\<And>C. C \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> C \<Longrightarrow> D \<le> C"
  then obtain C E where
    c_in_n: "C \<in> N" and
    c_true: "INTERP N \<Turnstile> C" and
    res_e: "unord_resolve C D E" and
    e_cex: "\<not> INTERP N \<Turnstile> E" and
    e_lt_d: "E < D"
    using unord_resolve_counterex_reducing by (metis (no_types))
  from c_in_n have "set_mset {#C#} \<subseteq> N"
    by auto
  moreover have "Infer {#C#} D E \<in> unord_\<Gamma>"
    unfolding unord_\<Gamma>_def using res_e by blast
  ultimately show
    "\<exists>CC E. set_mset CC \<subseteq> N \<and> INTERP N \<Turnstile>m CC \<and> Infer CC D E \<in> unord_\<Gamma> \<and> \<not> INTERP N \<Turnstile> E \<and> E < D"
    using c_in_n c_true e_cex e_lt_d by blast
next
  fix CC D E and I :: "'b interp"
  assume "Infer CC D E \<in> unord_\<Gamma>" and "I \<Turnstile>m CC" and "I \<Turnstile> D"
  then show "I \<Turnstile> E"
    by (clarsimp simp: unord_\<Gamma>_def true_cls_mset_def) (erule unord_resolve_sound, auto)
qed

lemmas clausal_logic_compact = unord_\<Gamma>_sound_counterex_reducing.clausal_logic_compact

end

text \<open>
Theorem 3.12, compactness of clausal logic, has finally been derived for a concrete inference
system:
\<close>

lemmas clausal_logic_compact = ground_resolution_without_selection.clausal_logic_compact

end
