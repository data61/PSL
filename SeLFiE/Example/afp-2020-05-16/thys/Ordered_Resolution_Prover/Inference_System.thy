(*  Title:       Refutational Inference Systems
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Refutational Inference Systems\<close>

theory Inference_System
  imports Herbrand_Interpretation
begin

text \<open>
This theory gathers results from Section 2.4 (``Refutational Theorem Proving''), 3 (``Standard
Resolution''), and 4.2 (``Counterexample-Reducing Inference Systems'') of Bachmair and Ganzinger's
chapter.
\<close>


subsection \<open>Preliminaries\<close>

text \<open>
Inferences have one distinguished main premise, any number of side premises, and a conclusion.
\<close>

datatype 'a inference =
  Infer (side_prems_of: "'a clause multiset") (main_prem_of: "'a clause") (concl_of: "'a clause")

abbreviation prems_of :: "'a inference \<Rightarrow> 'a clause multiset" where
  "prems_of \<gamma> \<equiv> side_prems_of \<gamma> + {#main_prem_of \<gamma>#}"

abbreviation concls_of :: "'a inference set \<Rightarrow> 'a clause set" where
  "concls_of \<Gamma> \<equiv> concl_of ` \<Gamma>"

(* FIXME: make an abbreviation *)
definition infer_from :: "'a clause set \<Rightarrow> 'a inference \<Rightarrow> bool" where
  "infer_from CC \<gamma> \<longleftrightarrow> set_mset (prems_of \<gamma>) \<subseteq> CC"

locale inference_system =
  fixes \<Gamma> :: "'a inference set"
begin

definition inferences_from :: "'a clause set \<Rightarrow> 'a inference set" where
  "inferences_from CC = {\<gamma>. \<gamma> \<in> \<Gamma> \<and> infer_from CC \<gamma>}"

definition inferences_between :: "'a clause set \<Rightarrow> 'a clause \<Rightarrow> 'a inference set" where
  "inferences_between CC C = {\<gamma>. \<gamma> \<in> \<Gamma> \<and> infer_from (CC \<union> {C}) \<gamma> \<and> C \<in># prems_of \<gamma>}"

lemma inferences_from_mono: "CC \<subseteq> DD \<Longrightarrow> inferences_from CC \<subseteq> inferences_from DD"
  unfolding inferences_from_def infer_from_def by fast

definition saturated :: "'a clause set \<Rightarrow> bool" where
  "saturated N \<longleftrightarrow> concls_of (inferences_from N) \<subseteq> N"

lemma saturatedD:
  assumes
    satur: "saturated N" and
    inf: "Infer CC D E \<in> \<Gamma>" and
    cc_subs_n: "set_mset CC \<subseteq> N" and
    d_in_n: "D \<in> N"
  shows "E \<in> N"
proof -
  have "Infer CC D E \<in> inferences_from N"
    unfolding inferences_from_def infer_from_def using inf cc_subs_n d_in_n by simp
  then have "E \<in> concls_of (inferences_from N)"
    unfolding image_iff by (metis inference.sel(3))
  then show "E \<in> N"
    using satur unfolding saturated_def by blast
qed

end

text \<open>
Satisfiability preservation is a weaker requirement than soundness.
\<close>

locale sat_preserving_inference_system = inference_system +
  assumes \<Gamma>_sat_preserving: "satisfiable N \<Longrightarrow> satisfiable (N \<union> concls_of (inferences_from N))"

locale sound_inference_system = inference_system +
  assumes \<Gamma>_sound: "Infer CC D E \<in> \<Gamma> \<Longrightarrow> I \<Turnstile>m CC \<Longrightarrow> I \<Turnstile> D \<Longrightarrow> I \<Turnstile> E"
begin

lemma \<Gamma>_sat_preserving:
  assumes sat_n: "satisfiable N"
  shows "satisfiable (N \<union> concls_of (inferences_from N))"
proof -
  obtain I where i: "I \<Turnstile>s N"
    using sat_n by blast
  then have "\<And>CC D E. Infer CC D E \<in> \<Gamma> \<Longrightarrow> set_mset CC \<subseteq> N \<Longrightarrow> D \<in> N \<Longrightarrow> I \<Turnstile> E"
    using \<Gamma>_sound unfolding true_clss_def true_cls_mset_def by (simp add: subset_eq)
  then have "\<And>\<gamma>. \<gamma> \<in> \<Gamma> \<Longrightarrow> infer_from N \<gamma> \<Longrightarrow> I \<Turnstile> concl_of \<gamma>"
    unfolding infer_from_def by (case_tac \<gamma>) clarsimp
  then have "I \<Turnstile>s concls_of (inferences_from N)"
    unfolding inferences_from_def image_def true_clss_def infer_from_def by blast
  then have "I \<Turnstile>s N \<union> concls_of (inferences_from N)"
    using i by simp
  then show ?thesis
    by blast
qed

sublocale sat_preserving_inference_system
  by unfold_locales (erule \<Gamma>_sat_preserving)

end

locale reductive_inference_system = inference_system \<Gamma> for \<Gamma> :: "('a :: wellorder) inference set" +
  assumes \<Gamma>_reductive: "\<gamma> \<in> \<Gamma> \<Longrightarrow> concl_of \<gamma> < main_prem_of \<gamma>"


subsection \<open>Refutational Completeness\<close>

text \<open>
Refutational completeness can be established once and for all for counterexample-reducing inference
systems. The material formalized here draws from both the general framework of Section 4.2 and the
concrete instances of Section 3.
\<close>

locale counterex_reducing_inference_system =
  inference_system \<Gamma> for \<Gamma> :: "('a :: wellorder) inference set" +
  fixes I_of :: "'a clause set \<Rightarrow> 'a interp"
  assumes \<Gamma>_counterex_reducing:
    "{#} \<notin> N \<Longrightarrow> D \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> D \<Longrightarrow> (\<And>C. C \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> C \<Longrightarrow> D \<le> C) \<Longrightarrow>
     \<exists>CC E. set_mset CC \<subseteq> N \<and> I_of N \<Turnstile>m CC \<and> Infer CC D E \<in> \<Gamma> \<and> \<not> I_of N \<Turnstile> E \<and> E < D"
begin

lemma ex_min_counterex:
  fixes N :: "('a :: wellorder) clause set"
  assumes "\<not> I \<Turnstile>s N"
  shows "\<exists>C \<in> N. \<not> I \<Turnstile> C \<and> (\<forall>D \<in> N. D < C \<longrightarrow> I \<Turnstile> D)"
proof -
  obtain C where "C \<in> N" and "\<not> I \<Turnstile> C"
    using assms unfolding true_clss_def by auto
  then have c_in: "C \<in> {C \<in> N. \<not> I \<Turnstile> C}"
    by blast
  show ?thesis
    using wf_eq_minimal[THEN iffD1, rule_format, OF wf_less_multiset c_in] by blast
qed

(* Theorem 4.4 (generalizes Theorems 3.9 and 3.16) *)

theorem saturated_model:
  assumes
    satur: "saturated N" and
    ec_ni_n: "{#} \<notin> N"
  shows "I_of N \<Turnstile>s N"
proof -
  have ec_ni_n: "{#} \<notin> N"
    using ec_ni_n by auto

  {
    assume "\<not> I_of N \<Turnstile>s N"
    then obtain D where
      d_in_n: "D \<in> N" and
      d_cex: "\<not> I_of N \<Turnstile> D" and
      d_min: "\<And>C. C \<in> N \<Longrightarrow> C < D \<Longrightarrow> I_of N \<Turnstile> C"
      by (meson ex_min_counterex)
    then obtain CC E where
      cc_subs_n: "set_mset CC \<subseteq> N" and
      inf_e: "Infer CC D E \<in> \<Gamma>" and
      e_cex: "\<not> I_of N \<Turnstile> E" and
      e_lt_d: "E < D"
      using \<Gamma>_counterex_reducing[OF ec_ni_n] not_less by metis
    from cc_subs_n inf_e have "E \<in> N"
      using d_in_n satur by (blast dest: saturatedD)
    then have False
      using e_cex e_lt_d d_min not_less by blast
  }
  then show ?thesis
    by satx
qed

text \<open>
Cf. Corollary 3.10:
\<close>

corollary saturated_complete: "saturated N \<Longrightarrow> \<not> satisfiable N \<Longrightarrow> {#} \<in> N"
  using saturated_model by blast

end


subsection \<open>Compactness\<close>

text \<open>
Bachmair and Ganzinger claim that compactness follows from refutational completeness but leave the
proof to the readers' imagination. Our proof relies on an inductive definition of saturation in
terms of a base set of clauses.
\<close>

context inference_system
begin

inductive_set saturate :: "'a clause set \<Rightarrow> 'a clause set" for CC :: "'a clause set" where
  base: "C \<in> CC \<Longrightarrow> C \<in> saturate CC"
| step: "Infer CC' D E \<in> \<Gamma> \<Longrightarrow> (\<And>C'. C' \<in># CC' \<Longrightarrow> C' \<in> saturate CC) \<Longrightarrow> D \<in> saturate CC \<Longrightarrow>
    E \<in> saturate CC"

lemma saturate_mono: "C \<in> saturate CC \<Longrightarrow> CC \<subseteq> DD \<Longrightarrow> C \<in> saturate DD"
  by (induct rule: saturate.induct) (auto intro: saturate.intros)

lemma saturated_saturate[simp, intro]: "saturated (saturate N)"
  unfolding saturated_def inferences_from_def infer_from_def image_def
  by clarify (rename_tac x, case_tac x, auto elim!: saturate.step)

lemma saturate_finite: "C \<in> saturate CC \<Longrightarrow> \<exists>DD. DD \<subseteq> CC \<and> finite DD \<and> C \<in> saturate DD"
proof (induct rule: saturate.induct)
  case (base C)
  then have "{C} \<subseteq> CC" and "finite {C}" and "C \<in> saturate {C}"
    by (auto intro: saturate.intros)
  then show ?case
    by blast
next
  case (step CC' D E)
  obtain DD_of where
    "\<And>C. C \<in># CC' \<Longrightarrow> DD_of C \<subseteq> CC \<and> finite (DD_of C) \<and> C \<in> saturate (DD_of C)"
    using step(3) by metis
  then have
    "(\<Union>C \<in> set_mset CC'. DD_of C) \<subseteq> CC"
    "finite (\<Union>C \<in> set_mset CC'. DD_of C) \<and> set_mset CC' \<subseteq> saturate (\<Union>C \<in> set_mset CC'. DD_of C)"
    by (auto intro: saturate_mono)
  then obtain DD where
    d_sub: "DD \<subseteq> CC" and d_fin: "finite DD" and in_sat_d: "set_mset CC' \<subseteq> saturate DD"
    by blast
  obtain EE where
    e_sub: "EE \<subseteq> CC" and e_fin: "finite EE" and in_sat_ee: "D \<in> saturate EE"
    using step(5) by blast
  have "DD \<union> EE \<subseteq> CC"
    using d_sub e_sub step(1) by fast
  moreover have "finite (DD \<union> EE)"
    using d_fin e_fin by fast
  moreover have "E \<in> saturate (DD \<union> EE)"
    using in_sat_d in_sat_ee step.hyps(1)
    by (blast intro: inference_system.saturate.step saturate_mono)
  ultimately show ?case
    by blast
qed

end

context sound_inference_system
begin

theorem saturate_sound: "C \<in> saturate CC \<Longrightarrow> I \<Turnstile>s CC \<Longrightarrow> I \<Turnstile> C"
  by (induct rule: saturate.induct) (auto simp: true_cls_mset_def true_clss_def \<Gamma>_sound)

end

context sat_preserving_inference_system
begin

text \<open>
This result surely holds, but we have yet to prove it. The challenge is: Every time a new clause is
introduced, we also get a new interpretation (by the definition of
\<open>sat_preserving_inference_system\<close>). But the interpretation we want here is then the one that
exists "at the limit". Maybe we can use compactness to prove it.
\<close>

theorem saturate_sat_preserving: "satisfiable CC \<Longrightarrow> satisfiable (saturate CC)"
  oops

end

locale sound_counterex_reducing_inference_system =
  counterex_reducing_inference_system + sound_inference_system
begin

text \<open>
Compactness of clausal logic is stated as Theorem 3.12 for the case of unordered ground resolution.
The proof below is a generalization to any sound counterexample-reducing inference system. The
actual theorem will become available once the locale has been instantiated with a concrete inference
system.
\<close>

theorem clausal_logic_compact:
  fixes N :: "('a :: wellorder) clause set"
  shows "\<not> satisfiable N \<longleftrightarrow> (\<exists>DD \<subseteq> N. finite DD \<and> \<not> satisfiable DD)"
proof
  assume "\<not> satisfiable N"
  then have "{#} \<in> saturate N"
    using saturated_complete saturated_saturate saturate.base unfolding true_clss_def by meson
  then have "\<exists>DD \<subseteq> N. finite DD \<and> {#} \<in> saturate DD"
    using saturate_finite by fastforce
  then show "\<exists>DD \<subseteq> N. finite DD \<and> \<not> satisfiable DD"
    using saturate_sound by auto
next
  assume "\<exists>DD \<subseteq> N. finite DD \<and> \<not> satisfiable DD"
  then show "\<not> satisfiable N"
    by (blast intro: true_clss_mono)
qed

end

end
