(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Asymmetric Variant of the Master Theorem\<close>

theory Asymmetric_Master_Theorem
imports
  Advice After
begin

text \<open>This variant of the Master Theorem fixes only a subset @{term Y}
      of @{term \<nu>LTL} subformulas and all conditions depend on the
      index @{term i}. While this does not lead to a simple DRA construction,
      but can be used to build NBAs and LDBAs.\<close>

lemma FG_advice_b1_helper:
  "\<psi> \<in> subfrmlsn \<phi> \<Longrightarrow> suffix i w \<Turnstile>\<^sub>n \<psi> \<Longrightarrow> suffix i w \<Turnstile>\<^sub>n \<psi>[\<F>\<G> \<phi> w]\<^sub>\<mu>"
proof -
  assume "\<psi> \<in> subfrmlsn \<phi>"

  then have "\<F>\<G> \<psi> (suffix i w) \<subseteq> \<F>\<G> \<phi> w"
    using \<F>\<G>_suffix subformulas\<^sub>\<nu>_subset unfolding \<F>\<G>_semantics' by fast

  moreover

  assume "suffix i w \<Turnstile>\<^sub>n \<psi>"

  ultimately show "suffix i w \<Turnstile>\<^sub>n \<psi>[\<F>\<G> \<phi> w]\<^sub>\<mu>"
    using FG_advice_b1 by blast
qed

lemma FG_advice_b2_helper:
  "S \<subseteq> \<G> \<phi> (suffix i w) \<Longrightarrow> i \<le> j \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<psi>[S]\<^sub>\<mu> \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<psi>"
proof -
  fix i j
  assume "S \<subseteq> \<G> \<phi> (suffix i w)" and "i \<le> j" and "suffix j w \<Turnstile>\<^sub>n \<psi>[S]\<^sub>\<mu>"

  then have "suffix j w \<Turnstile>\<^sub>n \<psi>[S \<inter> subformulas\<^sub>\<nu> \<psi>]\<^sub>\<mu>"
    using FG_advice_inter_subformulas by metis

  moreover

  have "S \<inter> subformulas\<^sub>\<nu> \<psi> \<subseteq> \<G> \<psi> (suffix i w)"
    using `S \<subseteq> \<G> \<phi> (suffix i w)` unfolding \<G>_semantics' by blast
  then have "S \<inter> subformulas\<^sub>\<nu> \<psi> \<subseteq> \<G> \<psi> (suffix j w)"
    using \<G>_suffix \<open>i \<le> j\<close> inf.absorb_iff2 le_Suc_ex by fastforce

  ultimately show "suffix j w \<Turnstile>\<^sub>n \<psi>"
    using FG_advice_b2 by blast
qed

lemma Y_\<G>:
  assumes
    Y_\<nu>: "Y \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  and
    Y_G_1: "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<in> Y \<longrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>)"
  and
    Y_G_2: "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<in> Y \<longrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1[Y]\<^sub>\<mu> or\<^sub>n \<psi>\<^sub>2[Y]\<^sub>\<mu>)"
  shows
    "Y \<subseteq> \<G> \<phi> (suffix i w)"
proof -
  \<comment> \<open>Custom induction rule with @{term size} as a partial order\<close>
  note induct = finite_ranking_induct[where f = size]

  have "finite Y"
    using Y_\<nu> finite_subset subformulas\<^sub>\<nu>_finite by auto

  then show ?thesis
    using assms
  proof (induction Y rule: induct)
    case (insert \<psi> S)

    show ?case
    proof (cases "\<psi> \<notin> S")
      assume "\<psi> \<notin> S"

      note FG_advice_insert = FG_advice_insert[OF `\<psi> \<notin> S`]

      {
        \<comment> \<open>Show @{term "S \<subseteq> \<G> \<phi> (suffix i w)"}\<close>

        {
          fix \<psi>\<^sub>1 \<psi>\<^sub>2
          assume "\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<in> S"

          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>\<^sub>2[insert \<psi> S]\<^sub>\<mu>"
            using insert(5) by blast

          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>\<^sub>2[S]\<^sub>\<mu>"
            using `\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<in> S` FG_advice_insert insert.hyps(2)
            by fastforce
        }

        moreover

        {
          fix \<psi>\<^sub>1 \<psi>\<^sub>2
          assume "\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<in> S"

          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1[insert \<psi> S]\<^sub>\<mu> or\<^sub>n \<psi>\<^sub>2[insert \<psi> S]\<^sub>\<mu>)"
            using insert(6) by blast

          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1[S]\<^sub>\<mu> or\<^sub>n \<psi>\<^sub>2[S]\<^sub>\<mu>)"
            using `\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<in> S` FG_advice_insert insert.hyps(2)
            by fastforce
        }

        ultimately

        have "S \<subseteq> \<G> \<phi> (suffix i w)"
          using insert.IH insert.prems(1) by blast
      }

      moreover

      {
        \<comment> \<open>Show @{term "\<psi> \<in> \<G> \<phi> (suffix i w)"}\<close>

        have "\<psi> \<in> subformulas\<^sub>\<nu> \<phi>"
          using insert.prems(1) by fast
        then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
          using subformulas\<^sub>\<nu>_semantics
        proof (cases \<psi>)
          case (Release_ltln \<psi>\<^sub>1 \<psi>\<^sub>2)

          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>\<^sub>2[insert \<psi> S]\<^sub>\<mu>"
            using insert.prems(2) by blast
          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>\<^sub>2[S]\<^sub>\<mu>"
            using Release_ltln FG_advice_insert by simp
          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>\<^sub>2"
            using FG_advice_b2_helper[OF `S \<subseteq> \<G> \<phi> (suffix i w)`] by auto
          then show ?thesis
            using Release_ltln globally_release
            by blast
        next
          case (WeakUntil_ltln \<psi>\<^sub>1 \<psi>\<^sub>2)

          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1[insert \<psi> S]\<^sub>\<mu> or\<^sub>n \<psi>\<^sub>2[insert \<psi> S]\<^sub>\<mu>)"
            using insert.prems(3) by blast
          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2)[S]\<^sub>\<mu>"
            using WeakUntil_ltln FG_advice_insert by simp
          then have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2)"
            using FG_advice_b2_helper[OF `S \<subseteq> \<G> \<phi> (suffix i w)`, of _ "\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2"]
            by force
          then show ?thesis
            unfolding WeakUntil_ltln semantics_ltln.simps
            by (metis order_refl suffix_suffix)
        qed fast+

        then have "\<psi> \<in> \<G> \<phi> (suffix i w)"
          unfolding \<G>_semantics using `\<psi> \<in> subformulas\<^sub>\<nu> \<phi>`
          by simp
      }

      ultimately show ?thesis
        by blast
    next
      assume "\<not> \<psi> \<notin> S"
      then have "insert \<psi> S = S"
        by auto
      then show ?thesis
        using insert by simp
    qed
  qed simp
qed

theorem asymmetric_master_theorem_ltr:
  assumes
    "w \<Turnstile>\<^sub>n \<phi>"
  obtains Y and i where
    "Y \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  and
    "suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[Y]\<^sub>\<mu>"
  and
    "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<in> Y \<longrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>)"
  and
    "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<in> Y \<longrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1[Y]\<^sub>\<mu> or\<^sub>n \<psi>\<^sub>2[Y]\<^sub>\<mu>)"
proof
  let ?Y = "\<F>\<G> \<phi> w"

  show "?Y \<subseteq> subformulas\<^sub>\<nu> \<phi>"
    by (rule \<F>\<G>_subformulas\<^sub>\<nu>)
next
  let ?Y = "\<F>\<G> \<phi> w"
  let ?i = "SOME i. ?Y = \<G> \<phi> (suffix i w)"

  have "suffix ?i w \<Turnstile>\<^sub>n af \<phi> (prefix ?i w)"
    using af_ltl_continuation \<open>w \<Turnstile>\<^sub>n \<phi>\<close> by fastforce
  then show "suffix ?i w \<Turnstile>\<^sub>n af \<phi> (prefix ?i w)[?Y]\<^sub>\<mu>"
    by (metis \<F>\<G>_suffix FG_advice_b1 \<F>\<G>_af order_refl)
next
  let ?Y = "\<F>\<G> \<phi> w"
  let ?i = "SOME i. ?Y = \<G> \<phi> (suffix i w)"

  have "\<exists>i. ?Y = \<G> \<phi> (suffix i w)"
    using suffix_\<nu>_stable \<F>\<G>_suffix unfolding \<nu>_stable_def MOST_nat
    by fast
  then have Y_G: "?Y = \<G> \<phi> (suffix ?i w)"
    by (metis (mono_tags, lifting) someI_ex)

  show "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<in> ?Y \<longrightarrow> suffix ?i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>2[?Y]\<^sub>\<mu>)"
  proof safe
    fix \<psi>\<^sub>1 \<psi>\<^sub>2
    assume "\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<in> ?Y"

    then have "suffix ?i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2)"
      using Y_G \<G>_semantics' by blast
    then have "suffix ?i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>\<^sub>2"
      by force

    moreover

    have "\<psi>\<^sub>2 \<in> subfrmlsn \<phi>"
      using \<F>\<G>_subfrmlsn `\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<in> ?Y` subfrmlsn_subset by force

    ultimately show "suffix ?i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>2 [?Y]\<^sub>\<mu>)"
      using FG_advice_b1_helper by fastforce
  qed
next
  let ?Y = "\<F>\<G> \<phi> w"
  let ?i = "SOME i. ?Y = \<G> \<phi> (suffix i w)"

  have "\<exists>i. ?Y = \<G> \<phi> (suffix i w)"
    using suffix_\<nu>_stable \<F>\<G>_suffix unfolding \<nu>_stable_def MOST_nat
    by fast
  then have Y_G: "?Y = \<G> \<phi> (suffix ?i w)"
    by (rule someI_ex)

  show "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<in> ?Y \<longrightarrow> suffix ?i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1[?Y]\<^sub>\<mu> or\<^sub>n \<psi>\<^sub>2[?Y]\<^sub>\<mu>)"
  proof safe
    fix \<psi>\<^sub>1 \<psi>\<^sub>2
    assume "\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<in> ?Y"

    then have "suffix ?i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2)"
      using Y_G \<G>_semantics' by blast
    then have "suffix ?i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2)"
      by force

    moreover

    have "\<psi>\<^sub>1 \<in> subfrmlsn \<phi>" and "\<psi>\<^sub>2 \<in> subfrmlsn \<phi>"
      using \<F>\<G>_subfrmlsn `\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<in> ?Y` subfrmlsn_subset by force+

    ultimately show "suffix ?i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1[?Y]\<^sub>\<mu> or\<^sub>n \<psi>\<^sub>2[?Y]\<^sub>\<mu>)"
      using FG_advice_b1_helper by fastforce
  qed
qed

theorem asymmetric_master_theorem_rtl:
  assumes
    1: "Y \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  and
    2: "suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[Y]\<^sub>\<mu>"
  and
    3: "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<in> Y \<longrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>)"
  and
    4: "\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<in> Y \<longrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1[Y]\<^sub>\<mu> or\<^sub>n \<psi>\<^sub>2[Y]\<^sub>\<mu>)"
  shows
    "w \<Turnstile>\<^sub>n \<phi>"
proof -
  have "suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)"
    by (metis assms Y_\<G> FG_advice_b2 \<G>_af)

  then show "w \<Turnstile>\<^sub>n \<phi>"
    using af_ltl_continuation by force
qed

theorem asymmetric_master_theorem:
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow>
    (\<exists>i. \<exists>Y \<subseteq> subformulas\<^sub>\<nu> \<phi>.
      suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[Y]\<^sub>\<mu>
      \<and> (\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2 \<in> Y \<longrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>))
      \<and> (\<forall>\<psi>\<^sub>1 \<psi>\<^sub>2. \<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2 \<in> Y \<longrightarrow> suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>\<^sub>1[Y]\<^sub>\<mu> or\<^sub>n \<psi>\<^sub>2[Y]\<^sub>\<mu>)))"
  by (metis asymmetric_master_theorem_ltr asymmetric_master_theorem_rtl)

end
