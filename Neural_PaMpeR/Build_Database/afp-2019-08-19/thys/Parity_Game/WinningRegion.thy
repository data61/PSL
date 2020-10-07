section \<open>Winning Regions\<close>

theory WinningRegion
imports
  Main
  WinningStrategy
begin

text \<open>
  Here we define winning regions of parity games.  The winning region for player \<open>p\<close> is the
  set of nodes from which \<open>p\<close> has a positional winning strategy.
\<close>

context ParityGame begin

definition "winning_region p \<equiv> { v \<in> V. \<exists>\<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v }"

lemma winning_regionI [intro]:
  assumes "v \<in> V" "strategy p \<sigma>" "winning_strategy p \<sigma> v"
  shows "v \<in> winning_region p"
  using assms unfolding winning_region_def by blast

lemma winning_region_in_V [simp]: "winning_region p \<subseteq> V" unfolding winning_region_def by blast

lemma winning_region_deadends:
  assumes "v \<in> VV p" "deadend v"
  shows "v \<in> winning_region p**"
proof
  show "v \<in> V" using \<open>v \<in> VV p\<close> by blast
  show "winning_strategy p** \<sigma>_arbitrary v" using assms winning_strategy_on_deadends by simp
qed simp

subsection \<open>Paths in Winning Regions\<close>

lemma (in vmc_path) paths_stay_in_winning_region:
  assumes \<sigma>': "strategy p \<sigma>'" "winning_strategy p \<sigma>' v0"
    and \<sigma>: "\<And>v. v \<in> winning_region p \<Longrightarrow> \<sigma>' v = \<sigma> v"
  shows "lset P \<subseteq> winning_region p"
proof
  fix x assume "x \<in> lset P"
  thus "x \<in> winning_region p" using assms vmc_path_axioms
  proof (induct arbitrary: v0 rule: llist_set_induct)
    case (find P v0)
    interpret vmc_path G P v0 p \<sigma> using find.prems(4) .
    show ?case using P_v0 \<sigma>'(1) find.prems(2) v0_V unfolding winning_region_def by blast
  next
    case (step P x v0)
    interpret vmc_path G P v0 p \<sigma> using step.prems(4) .
    show ?case proof (cases)
      assume "lnull (ltl P)"
      thus ?thesis using P_lnull_ltl_LCons step.hyps(2) by auto
    next
      assume "\<not>lnull (ltl P)"
      then interpret vmc_path_no_deadend G P v0 p \<sigma> using P_no_deadend_v0 by unfold_locales
      have "winning_strategy p \<sigma>' w0" proof (cases)
        assume "v0 \<in> VV p"
        hence "winning_strategy p \<sigma>' (\<sigma>' v0)"
          using strategy_extends_VVp local.step(4) step.prems(2) v0_no_deadend by blast
        moreover have "\<sigma> v0 = w0" using v0_conforms \<open>v0 \<in> VV p\<close> by blast
        moreover have "\<sigma>' v0 = \<sigma> v0"
          using \<sigma> assms(1) step.prems(2) v0_V unfolding winning_region_def by blast
        ultimately show ?thesis by simp
      next
        assume "v0 \<notin> VV p"
        thus ?thesis using v0_V strategy_extends_VVpstar step(4) step.prems(2) by simp
      qed
      thus ?thesis using step.hyps(3) step(4) \<sigma> vmc_path_ltl by blast
    qed
  qed
qed

lemma (in vmc_path) path_hits_winning_region_is_winning:
  assumes \<sigma>': "strategy p \<sigma>'" "\<And>v. v \<in> winning_region p \<Longrightarrow> winning_strategy p \<sigma>' v"
    and \<sigma>: "\<And>v. v \<in> winning_region p \<Longrightarrow> \<sigma>' v = \<sigma> v"
    and P: "lset P \<inter> winning_region p \<noteq> {}"
  shows "winning_path p P"
proof-
  obtain n where n: "enat n < llength P" "P $ n \<in> winning_region p"
    using P by (meson lset_intersect_lnth)
  define P' where "P' = ldropn n P"
  then interpret P': vmc_path G P' "P $ n" p \<sigma>
    unfolding P'_def using vmc_path_ldropn n(1) by blast
  have "winning_strategy p \<sigma>' (P $ n)" using \<sigma>'(2) n(2) by blast
  hence "lset P' \<subseteq> winning_region p"
    using P'.paths_stay_in_winning_region[OF \<sigma>'(1) _ \<sigma>]
    by blast
  hence "\<And>v. v \<in> lset P' \<Longrightarrow> \<sigma> v = \<sigma>' v" using \<sigma> by auto
  hence "path_conforms_with_strategy p P' \<sigma>'"
    using path_conforms_with_strategy_irrelevant_updates P'.P_conforms
    by blast
  then interpret P': vmc_path G P' "P $ n" p \<sigma>' using P'.conforms_to_another_strategy by blast
  have "winning_path p P'" using \<sigma>'(2) n(2) P'.vmc_path_axioms winning_strategy_def by blast
  thus "winning_path p P" unfolding P'_def using winning_path_drop_add n(1) P_valid by blast
qed

subsection \<open>Irrelevant Updates\<close>

text \<open>Updating a winning strategy outside of the winning region is irrelevant.\<close>

lemma winning_strategy_updates:
  assumes \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v0"
    and v: "v \<notin> winning_region p" "v\<rightarrow>w"
  shows "winning_strategy p (\<sigma>(v := w)) v0"
proof
  fix P assume "vmc_path G P v0 p (\<sigma>(v := w))"
  then interpret vmc_path G P v0 p "\<sigma>(v := w)" .
  have "\<And>v'. v' \<in> winning_region p \<Longrightarrow> \<sigma> v' = (\<sigma>(v := w)) v'" using v by auto
  hence "v \<notin> lset P" using v paths_stay_in_winning_region \<sigma> unfolding winning_region_def by blast
  hence "path_conforms_with_strategy p P \<sigma>"
    using P_conforms path_conforms_with_strategy_irrelevant' by blast
  thus "winning_path p P" using conforms_to_another_strategy \<sigma>(2) winning_strategy_def by blast
qed

subsection \<open>Extending Winning Regions\<close>

lemma winning_region_extends_VVp:
  assumes v: "v \<in> VV p" "v\<rightarrow>w" and w: "w \<in> winning_region p"
  shows "v \<in> winning_region p"
proof (rule ccontr)
  obtain \<sigma> where \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> w"
    using w unfolding winning_region_def by blast
  let ?\<sigma> = "\<sigma>(v := w)"
  assume contra: "v \<notin> winning_region p"
  moreover have "strategy p ?\<sigma>" using valid_strategy_updates \<sigma>(1) \<open>v\<rightarrow>w\<close> by blast
  moreover hence "winning_strategy p ?\<sigma> v"
    using winning_strategy_updates \<sigma> contra v strategy_extends_backwards_VVp
    by auto
  ultimately show False using \<open>v\<rightarrow>w\<close> unfolding winning_region_def by auto
qed

text \<open>
  Unfortunately, we cannot prove the corresponding theorem \<open>winning_region_extends_VVpstar\<close>
  for @{term "VV p**"}-nodes yet.
  First, we need to show that there exists a uniform winning strategy on @{term "winning_region p"}.
  We will prove \<open>winning_region_extends_VVpstar\<close> as soon as we have this.
\<close>

end \<comment> \<open>context ParityGame\<close>

end
