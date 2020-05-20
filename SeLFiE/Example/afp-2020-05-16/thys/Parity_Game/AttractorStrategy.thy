section \<open>Attractor Strategies\<close>

theory AttractorStrategy
imports
  Main
  Attractor UniformStrategy
begin

text \<open>This section proves that every attractor set has an attractor strategy.\<close>

context ParityGame begin

lemma strategy_attracts_extends_VVp:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts p \<sigma> S W"
    and v0: "v0 \<in> VV p" "v0 \<in> directly_attracted p S" "v0 \<notin> S"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 (insert v0 S) W"
proof-
  from v0(1,2) obtain w where "v0\<rightarrow>w" "w \<in> S" using directly_attracted_def by blast
  from \<open>w \<in> S\<close> \<sigma>(2) have "strategy_attracts_via p \<sigma> w S W" unfolding strategy_attracts_def by blast
  let ?\<sigma> = "\<sigma>(v0 := w)" \<comment> \<open>Extend @{term \<sigma>} to the new node.\<close>
  have "strategy p ?\<sigma>" using \<sigma>(1) \<open>v0\<rightarrow>w\<close> valid_strategy_updates by blast
  moreover have "strategy_attracts_via p ?\<sigma> v0 (insert v0 S) W" proof
    fix P
    assume "vmc_path G P v0 p ?\<sigma>"
    then interpret vmc_path G P v0 p ?\<sigma> .
    have "\<not>deadend v0" using \<open>v0\<rightarrow>w\<close> by blast
    then interpret vmc_path_no_deadend G P v0 p ?\<sigma> by unfold_locales

    define P'' where [simp]: "P'' = ltl P"
    have "lhd P'' = w" using v0(1) v0_conforms w0_def by auto
    hence "vmc_path G P'' w p ?\<sigma>" using vmc_path_ltl by (simp add: w0_def)

    have *: "v0 \<notin> S - W" using \<open>v0 \<notin> S\<close> by blast
    have "override_on (\<sigma>(v0 := w)) \<sigma> (S - W) = ?\<sigma>"
      by (rule ext) (metis * fun_upd_def override_on_def)
    hence "strategy_attracts p ?\<sigma> S W"
      using strategy_attracts_irrelevant_override[OF \<sigma>(2,1) \<open>strategy p ?\<sigma>\<close>] by simp
    hence "strategy_attracts_via p ?\<sigma> w S W" unfolding strategy_attracts_def
      using \<open>w \<in> S\<close> by blast
    hence "visits_via P'' S W" unfolding strategy_attracts_via_def
      using \<open>vmc_path G P'' w p ?\<sigma>\<close> by blast
    thus "visits_via P (insert v0 S) W"
      using visits_via_LCons[of "ltl P" S W v0] P_LCons by simp
  qed
  ultimately show ?thesis by blast
qed

lemma strategy_attracts_extends_VVpstar:
  assumes \<sigma>: "strategy_attracts p \<sigma> S W"
    and v0: "v0 \<notin> VV p" "v0 \<in> directly_attracted p S"
  shows "strategy_attracts_via p \<sigma> v0 (insert v0 S) W"
proof
  fix P
  assume "vmc_path G P v0 p \<sigma>"
  then interpret vmc_path G P v0 p \<sigma> .
  have "\<not>deadend v0" using v0(2) directly_attracted_contains_no_deadends by blast
  then interpret vmc_path_no_deadend G P v0 p \<sigma> by unfold_locales
  have "visits_via (ltl P) S W"
    using vmc_path.strategy_attractsE[OF vmc_path_ltl \<sigma>] v0 directly_attracted_def by simp
  thus "visits_via P (insert v0 S) W" using visits_via_LCons[of "ltl P" S W v0] P_LCons by simp
qed

lemma attractor_has_strategy_single:
  assumes "W \<subseteq> V"
    and v0_def: "v0 \<in> attractor p W" (is "_ \<in> ?A")
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 ?A W"
using assms proof (induct arbitrary: v0 rule: attractor_set_induction)
  case (step S)
  have "v0 \<in> W \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 {} W"
    using strategy_attracts_via_trivial valid_arbitrary_strategy by blast
  moreover {
    assume *: "v0 \<in> directly_attracted p S" "v0 \<notin> S"
    from assms(1) step.hyps(1) step.hyps(2)
      have "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> S W"
      using merge_attractor_strategies by auto
    with *
      have "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v0 (insert v0 S) W"
      using strategy_attracts_extends_VVp strategy_attracts_extends_VVpstar by blast
  }
  ultimately show ?case
    using step.prems step.hyps(2)
    attractor_strategy_on_extends[of p _ v0 "insert v0 S" W "W \<union> S \<union> directly_attracted p S"]
    attractor_strategy_on_extends[of p _ v0 "S"           W "W \<union> S \<union> directly_attracted p S"]
    attractor_strategy_on_extends[of p _ v0 "{}"          W "W \<union> S \<union> directly_attracted p S"]
    by blast
next
  case (union M)
  hence "\<exists>S. S \<in> M \<and> v0 \<in> S" by blast
  thus ?case by (meson Union_upper attractor_strategy_on_extends union.hyps)
qed

subsection \<open>Existence\<close>

text \<open>Prove that every attractor set has an attractor strategy.\<close>

theorem attractor_has_strategy:
  assumes "W \<subseteq> V"
  shows "\<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts p \<sigma> (attractor p W) W"
proof-
  let ?A = "attractor p W"
  have "?A \<subseteq> V" by (simp add: \<open>W \<subseteq> V\<close> attractor_in_V)
  moreover
    have "\<And>v. v \<in> ?A \<Longrightarrow> \<exists>\<sigma>. strategy p \<sigma> \<and> strategy_attracts_via p \<sigma> v ?A W"
    using \<open>W \<subseteq> V\<close> attractor_has_strategy_single by blast
  ultimately show ?thesis using merge_attractor_strategies \<open>W \<subseteq> V\<close> by blast
qed

end \<comment> \<open>context ParityGame\<close>

end
