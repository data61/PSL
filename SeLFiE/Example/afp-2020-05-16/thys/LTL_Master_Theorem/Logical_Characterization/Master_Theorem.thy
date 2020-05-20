(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>The Master Theorem\<close>

theory Master_Theorem
imports
  Advice After
begin

subsection \<open>Checking @{term "X \<subseteq> \<G>\<F> \<phi> w"} and @{term "Y \<subseteq> \<F>\<G> \<phi> w"}\<close>

lemma X_\<G>\<F>_Y_\<F>\<G>:
  assumes
    X_\<mu>: "X \<subseteq> subformulas\<^sub>\<mu> \<phi>"
  and
    Y_\<nu>: "Y \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  and
    X_GF: "\<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>)"
  and
    Y_FG: "\<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>)"
  shows
    "X \<subseteq> \<G>\<F> \<phi> w \<and> Y \<subseteq> \<F>\<G> \<phi> w"
proof -
  \<comment> \<open>Custom induction rule with @{term size} as a partial order\<close>
  note induct = finite_ranking_induct[where f = size]

  have "finite (X \<union> Y)"
    using subformulas\<^sub>\<mu>_finite subformulas\<^sub>\<nu>_finite X_\<mu> Y_\<nu> finite_subset
    by blast+

  then show ?thesis
    using assms
  proof (induction "X \<union> Y" arbitrary: X Y \<phi> rule: induct)
    case (insert \<psi> S)

    note IH = insert(3)
    note insert_S = `insert \<psi> S = X \<union> Y`
    note X_\<mu> = `X \<subseteq> subformulas\<^sub>\<mu> \<phi>`
    note Y_\<nu> = `Y \<subseteq> subformulas\<^sub>\<nu> \<phi>`
    note X_GF = `\<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>)`
    note Y_FG = `\<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>)`

    from X_\<mu> Y_\<nu> have "X \<inter> Y = {}"
      using subformulas\<^sub>\<mu>\<^sub>\<nu>_disjoint by fast

    from insert_S X_\<mu> Y_\<nu> have "\<psi> \<in> subfrmlsn \<phi>"
      using subformulas\<^sub>\<mu>_subfrmlsn subformulas\<^sub>\<nu>_subfrmlsn by blast

    show ?case
    proof (cases "\<psi> \<notin> S", cases "\<psi> \<in> X")
      assume "\<psi> \<notin> S" and "\<psi> \<in> X"

      {
        \<comment> \<open>Show @{term "X - {\<psi>} \<subseteq> \<G>\<F> \<phi> w"} and @{term "Y \<subseteq> \<F>\<G> \<phi> w"}\<close>

        then have "\<psi> \<notin> Y"
          using `X \<inter> Y = {}` by auto
        then have "S = (X - {\<psi>}) \<union> Y"
          using insert_S `\<psi> \<notin> S` by fast

        moreover

        have "\<forall>\<psi>' \<in> Y. \<psi>'[X - {\<psi>}]\<^sub>\<nu> = \<psi>'[X]\<^sub>\<nu>"
          using GF_advice_minus_size insert(1,2,4) `\<psi> \<notin> Y` by fast

        ultimately have "X - {\<psi>} \<subseteq> \<G>\<F> \<phi> w" and "Y \<subseteq> \<F>\<G> \<phi> w"
          using IH[of "X - {\<psi>}" Y \<phi>] X_\<mu> Y_\<nu> X_GF Y_FG by auto
      }

      moreover

      {
        \<comment> \<open>Show @{term "\<psi> \<in> \<G>\<F> \<phi> w"}\<close>

        have "w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>)"
          using X_GF `\<psi> \<in> X` by simp
        then have "\<exists>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>[Y]\<^sub>\<mu>"
          unfolding GF_Inf_many by simp

        moreover

        from Y_\<nu> have "finite Y"
          using subformulas\<^sub>\<nu>_finite finite_subset by auto

        have "\<forall>\<phi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<phi>)"
          using `Y \<subseteq> \<F>\<G> \<phi> w` by (blast dest: \<F>\<G>_elim)
        then have "\<forall>\<phi> \<in> Y. \<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<phi>"
          using FG_suffix_G by blast
        then have "\<forall>\<^sub>\<infinity>i. \<forall>\<phi> \<in> Y. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<phi>"
          using `finite Y` eventually_ball_finite by fast

        ultimately

        have "\<exists>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>[Y]\<^sub>\<mu> \<and> (\<forall>\<phi> \<in> Y. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<phi>)"
          using INFM_conjI by auto
        then have "\<exists>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>"
          by (elim frequently_elim1) (metis FG_advice_b2_helper)
        then have "w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)"
          unfolding GF_Inf_many by simp
        then have "\<psi> \<in> \<G>\<F> \<phi> w"
          unfolding \<G>\<F>_semantics using `\<psi> \<in> X` X_\<mu> by auto
      }

      ultimately show ?thesis
        by auto
    next
      assume "\<psi> \<notin> S" and "\<psi> \<notin> X"
      then have "\<psi> \<in> Y"
        using insert by fast

      {
        \<comment> \<open>Show @{term "X \<subseteq> \<G>\<F> \<phi> w"} and @{term "Y - {\<psi>} \<subseteq> \<F>\<G> \<phi> w"}\<close>

        then have "S \<inter> X = X"
          using insert `\<psi> \<notin> X` by fast
        then have "S = X \<union> (Y - {\<psi>})"
          using insert_S `\<psi> \<notin> S` by fast

        moreover

        have "\<forall>\<psi>' \<in> X. \<psi>'[Y - {\<psi>}]\<^sub>\<mu> = \<psi>'[Y]\<^sub>\<mu>"
          using FG_advice_minus_size insert(1,2,4) `\<psi> \<notin> X` by fast

        ultimately have "X \<subseteq> \<G>\<F> \<phi> w" and "Y - {\<psi>} \<subseteq> \<F>\<G> \<phi> w"
          using IH[of X "Y - {\<psi>}" \<phi>] X_\<mu> Y_\<nu> X_GF Y_FG by auto
      }

      moreover

      {
        \<comment> \<open>Show @{term "\<psi> \<in> \<F>\<G> \<phi> w"}\<close>

        have "w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>)"
          using Y_FG `\<psi> \<in> Y` by simp
        then have "\<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>[X]\<^sub>\<nu>"
          unfolding FG_Alm_all by simp

        moreover

        have "\<forall>\<phi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<phi>)"
          using `X \<subseteq> \<G>\<F> \<phi> w` by (blast dest: \<G>\<F>_elim)
        then have "\<forall>\<^sub>\<infinity>i. \<forall>\<phi> \<in> X. suffix i w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<phi>)"
          by simp

        ultimately

        have "\<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>[X]\<^sub>\<nu> \<and> (\<forall>\<phi> \<in> X. suffix i w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<phi>))"
          using MOST_conjI by auto
        then have "\<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>"
          by (elim MOST_mono) (metis GF_advice_a2_helper)
        then have "w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>)"
          unfolding FG_Alm_all by simp
        then have "\<psi> \<in> \<F>\<G> \<phi> w"
          unfolding \<F>\<G>_semantics using `\<psi> \<in> Y` Y_\<nu> by auto
      }

      ultimately show ?thesis
        by auto
    next
      assume "\<not> \<psi> \<notin> S"
      then have "S = X \<union> Y"
        using insert by fast
      then show ?thesis
        using insert by auto
    qed
  qed fast
qed


lemma \<G>\<F>_implies_GF:
  "\<forall>\<psi> \<in> \<G>\<F> \<phi> w. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[\<F>\<G> \<phi> w]\<^sub>\<mu>)"
proof safe
  fix \<psi>
  assume "\<psi> \<in> \<G>\<F> \<phi> w"

  then have "\<exists>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>"
    using \<G>\<F>_elim GF_Inf_many by blast

  moreover

  have "\<psi> \<in> subfrmlsn \<phi>"
    using `\<psi> \<in> \<G>\<F> \<phi> w` \<G>\<F>_subfrmlsn by blast

  then have "\<And>i w. \<F>\<G> \<psi> (suffix i w) \<subseteq> \<F>\<G> \<phi> w"
    using \<F>\<G>_suffix \<F>\<G>_subset by blast

  ultimately have "\<exists>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>[\<F>\<G> \<phi> w]\<^sub>\<mu>"
    by (elim frequently_elim1) (metis FG_advice_b1)

  then show "w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[\<F>\<G> \<phi> w]\<^sub>\<mu>)"
    unfolding GF_Inf_many by simp
qed


lemma \<F>\<G>_implies_FG:
  "\<forall>\<psi> \<in> \<F>\<G> \<phi> w. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[\<G>\<F> \<phi> w]\<^sub>\<nu>)"
proof safe
  fix \<psi>
  assume "\<psi> \<in> \<F>\<G> \<phi> w"

  then have "\<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>"
    using \<F>\<G>_elim FG_Alm_all by blast

  moreover

  {
    have "\<psi> \<in> subfrmlsn \<phi>"
      using `\<psi> \<in> \<F>\<G> \<phi> w` \<F>\<G>_subfrmlsn by blast

    moreover have "\<forall>\<^sub>\<infinity>i. \<G>\<F> \<psi> (suffix i w) = \<F> \<psi> (suffix i w)"
      using suffix_\<mu>_stable unfolding \<mu>_stable_def by blast

    ultimately have "\<forall>\<^sub>\<infinity>i. \<F> \<psi> (suffix i w) \<subseteq> \<G>\<F> \<phi> w"
      unfolding MOST_nat_le by (metis \<G>\<F>_subset \<G>\<F>_suffix)
  }

  ultimately have "\<forall>\<^sub>\<infinity>i. \<F> \<psi> (suffix i w) \<subseteq> \<G>\<F> \<phi> w \<and> suffix i w \<Turnstile>\<^sub>n \<psi>"
    using eventually_conj by auto

  then have "\<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile>\<^sub>n \<psi>[\<G>\<F> \<phi> w]\<^sub>\<nu>"
    using GF_advice_a1 by (elim eventually_mono) auto

  then show "w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[\<G>\<F> \<phi> w]\<^sub>\<nu>)"
    unfolding FG_Alm_all by simp
qed


subsection \<open>Putting the pieces together: The Master Theorem\<close>

theorem master_theorem_ltr:
  assumes
    "w \<Turnstile>\<^sub>n \<phi>"
  obtains X and Y where
    "X \<subseteq> subformulas\<^sub>\<mu> \<phi>"
  and
    "Y \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  and
    "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>"
  and
    "\<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>)"
  and
    "\<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>)"
proof
  show "\<G>\<F> \<phi> w \<subseteq> subformulas\<^sub>\<mu> \<phi>"
    by (rule \<G>\<F>_subformulas\<^sub>\<mu>)
next
  show "\<F>\<G> \<phi> w \<subseteq> subformulas\<^sub>\<nu> \<phi>"
    by (rule \<F>\<G>_subformulas\<^sub>\<nu>)
next
  obtain i where "\<G>\<F> \<phi> (suffix i w) = \<F> \<phi> (suffix i w)"
    using suffix_\<mu>_stable unfolding MOST_nat \<mu>_stable_def by fast
  then have "\<F> (af \<phi> (prefix i w)) (suffix i w) \<subseteq> \<G>\<F> \<phi> w"
    using \<G>\<F>_af \<F>_af \<G>\<F>_suffix by fast

  moreover

  have "suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)"
    using af_ltl_continuation `w \<Turnstile>\<^sub>n \<phi>` by fastforce

  ultimately show "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[\<G>\<F> \<phi> w]\<^sub>\<nu>"
    using GF_advice_a1 by blast
next
  show "\<forall>\<psi> \<in> \<G>\<F> \<phi> w. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[\<F>\<G> \<phi> w]\<^sub>\<mu>)"
    by (rule \<G>\<F>_implies_GF)
next
  show "\<forall>\<psi> \<in> \<F>\<G> \<phi> w. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[\<G>\<F> \<phi> w]\<^sub>\<nu>)"
    by (rule \<F>\<G>_implies_FG)
qed

theorem master_theorem_rtl:
  assumes
    "X \<subseteq> subformulas\<^sub>\<mu> \<phi>"
  and
    "Y \<subseteq> subformulas\<^sub>\<nu> \<phi>"
  and
    1: "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>"
  and
    2: "\<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>)"
  and
    3: "\<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>)"
  shows
    "w \<Turnstile>\<^sub>n \<phi>"
proof -
  from 1 obtain i where "suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>"
    by blast

  moreover

  from assms have "X \<subseteq> \<G>\<F> \<phi> w"
    using X_\<G>\<F>_Y_\<F>\<G> by blast
  then have "X \<subseteq> \<G>\<F> \<phi> (suffix i w)"
    using \<G>\<F>_suffix by fast

  ultimately have "suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)"
    using GF_advice_a2 \<G>\<F>_af by metis
  then show "w \<Turnstile>\<^sub>n \<phi>"
    using af_ltl_continuation by force
qed

theorem master_theorem:
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow>
    (\<exists>X \<subseteq> subformulas\<^sub>\<mu> \<phi>.
      (\<exists>Y \<subseteq> subformulas\<^sub>\<nu> \<phi>.
        (\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>)
        \<and> (\<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>))
        \<and> (\<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>))))"
  by (metis master_theorem_ltr master_theorem_rtl)



subsection \<open>The Master Theorem on Languages\<close>

definition "L\<^sub>1 \<phi> X = {w. \<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>}"

definition "L\<^sub>2 X Y = {w. \<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>)}"

definition "L\<^sub>3 X Y = {w. \<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>)}"

corollary master_theorem_language:
  "language_ltln \<phi> = \<Union> {L\<^sub>1 \<phi> X \<inter> L\<^sub>2 X Y \<inter> L\<^sub>3 X Y | X Y. X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<and> Y \<subseteq> subformulas\<^sub>\<nu> \<phi>}"
proof safe
  fix w
  assume "w \<in> language_ltln \<phi>"

  then have "w \<Turnstile>\<^sub>n \<phi>"
    unfolding language_ltln_def by simp

  then obtain X Y where "X \<subseteq> subformulas\<^sub>\<mu> \<phi>" and "Y \<subseteq> subformulas\<^sub>\<nu> \<phi>"
    and "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>"
    and "\<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>)"
    and "\<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>)"
    using master_theorem_ltr by metis

  then have "w \<in> L\<^sub>1 \<phi> X" and "w \<in> L\<^sub>2 X Y" and "w \<in> L\<^sub>3 X Y"
    unfolding L\<^sub>1_def L\<^sub>2_def L\<^sub>3_def by simp+

  then show "w \<in> \<Union> {L\<^sub>1 \<phi> X \<inter> L\<^sub>2 X Y \<inter> L\<^sub>3 X Y | X Y. X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<and> Y \<subseteq> subformulas\<^sub>\<nu> \<phi>}"
    using `X \<subseteq> subformulas\<^sub>\<mu> \<phi>` `Y \<subseteq> subformulas\<^sub>\<nu> \<phi>` by blast
next
  fix w X Y
  assume "X \<subseteq> subformulas\<^sub>\<mu> \<phi>" and "Y \<subseteq> subformulas\<^sub>\<nu> \<phi>"
    and "w \<in> L\<^sub>1 \<phi> X" and "w \<in> L\<^sub>2 X Y" and "w \<in> L\<^sub>3 X Y"

  then show "w \<in> language_ltln \<phi>"
    unfolding language_ltln_def L\<^sub>1_def L\<^sub>2_def L\<^sub>3_def
    using master_theorem_rtl by blast
qed

end
