section \<open>Positional Strategies\<close>

theory Strategy
imports
  Main
  ParityGame
begin

subsection \<open>Definitions\<close>

text \<open>
  A \emph{strategy} is simply a function from nodes to nodes
  We only consider positional strategies.
\<close>
type_synonym 'a Strategy = "'a \<Rightarrow> 'a"

text \<open>
  A \emph{valid} strategy for player @{term p} is a function assigning a successor to each node
  in @{term "VV p"}.\<close>
definition (in ParityGame) strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  "strategy p \<sigma> \<equiv> \<forall>v \<in> VV p. \<not>deadend v \<longrightarrow> v\<rightarrow>\<sigma> v"

lemma (in ParityGame) strategyI [intro]:
  "(\<And>v. \<lbrakk> v \<in> VV p; \<not>deadend v \<rbrakk> \<Longrightarrow> v\<rightarrow>\<sigma> v) \<Longrightarrow> strategy p \<sigma>"
  unfolding strategy_def by blast

subsection \<open>Strategy-Conforming Paths\<close>

text \<open>
  If @{term "path_conforms_with_strategy p P \<sigma>"} holds, then we call @{term P} a
  \emph{@{term \<sigma>}-path}.
  This means that @{term P} follows @{term \<sigma>} on all nodes of player @{term p}
  except maybe the last node on the path.
\<close>
coinductive (in ParityGame) path_conforms_with_strategy
  :: "Player \<Rightarrow> 'a Path \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
  path_conforms_LNil:  "path_conforms_with_strategy p LNil \<sigma>"
| path_conforms_LCons_LNil: "path_conforms_with_strategy p (LCons v LNil) \<sigma>"
| path_conforms_VVp: "\<lbrakk> v \<in> VV p; w = \<sigma> v; path_conforms_with_strategy p (LCons w Ps) \<sigma> \<rbrakk>
    \<Longrightarrow> path_conforms_with_strategy p (LCons v (LCons w Ps)) \<sigma>"
| path_conforms_VVpstar: "\<lbrakk> v \<notin> VV p; path_conforms_with_strategy p Ps \<sigma> \<rbrakk>
    \<Longrightarrow> path_conforms_with_strategy p (LCons v Ps) \<sigma>"

text \<open>
  Define a locale for valid maximal paths that conform to a given strategy, because we need
  this concept quite often.  However, we are not yet able to add interesting lemmas to this locale.
  We will do this at the end of this section, where we have more lemmas available.
\<close>
locale vmc_path = vm_path +
  fixes p \<sigma> assumes P_conforms [simp]: "path_conforms_with_strategy p P \<sigma>"

text \<open>
  Similary, define a locale for valid maximal paths that conform to given strategies for both
  players.
\<close>
locale vmc2_path = comp?: vmc_path G P v0 "p**" \<sigma>' + vmc_path G P v0 p \<sigma>
  for G P v0 p \<sigma> \<sigma>'


subsection \<open>An Arbitrary Strategy\<close>

context ParityGame begin

text \<open>
  Define an arbitrary strategy.  This is useful to define other strategies by overriding part of
  this strategy.
\<close>
definition "\<sigma>_arbitrary \<equiv> \<lambda>v. SOME w. v\<rightarrow>w"

lemma valid_arbitrary_strategy [simp]: "strategy p \<sigma>_arbitrary" proof
  fix v assume "\<not>deadend v"
  thus "v \<rightarrow> \<sigma>_arbitrary v" unfolding \<sigma>_arbitrary_def using someI_ex[of "\<lambda>w. v\<rightarrow>w"] by blast
qed

subsection \<open>Valid Strategies\<close>

lemma valid_strategy_updates: "\<lbrakk> strategy p \<sigma>; v0\<rightarrow>w0 \<rbrakk> \<Longrightarrow> strategy p (\<sigma>(v0 := w0))"
  unfolding strategy_def by auto

lemma valid_strategy_updates_set:
  assumes "strategy p \<sigma>" "\<And>v. \<lbrakk> v \<in> A; v \<in> VV p; \<not>deadend v \<rbrakk> \<Longrightarrow> v\<rightarrow>\<sigma>' v"
  shows "strategy p (override_on \<sigma> \<sigma>' A)"
  unfolding strategy_def by (metis assms override_on_def strategy_def)

lemma valid_strategy_updates_set_strong:
  assumes "strategy p \<sigma>" "strategy p \<sigma>'"
  shows "strategy p (override_on \<sigma> \<sigma>' A)"
  using assms(1) assms(2)[unfolded strategy_def] valid_strategy_updates_set by simp

lemma subgame_strategy_stays_in_subgame:
  assumes \<sigma>: "ParityGame.strategy (subgame V') p \<sigma>"
    and "v \<in> ParityGame.VV (subgame V') p" "\<not>Digraph.deadend (subgame V') v"
  shows "\<sigma> v \<in> V'"
proof-
  interpret G': ParityGame "subgame V'" using subgame_ParityGame .
  have "\<sigma> v \<in> V\<^bsub>subgame V'\<^esub>" using assms unfolding G'.strategy_def G'.edges_are_in_V(2) by blast
  thus "\<sigma> v \<in> V'" by (metis Diff_iff IntE subgame_VV Player.distinct(2))
qed

lemma valid_strategy_supergame:
  assumes \<sigma>: "strategy p \<sigma>"
    and \<sigma>': "ParityGame.strategy (subgame V') p \<sigma>'"
    and G'_no_deadends: "\<And>v. v \<in> V' \<Longrightarrow> \<not>Digraph.deadend (subgame V') v"
  shows "strategy p (override_on \<sigma> \<sigma>' V')" (is "strategy p ?\<sigma>")
proof
  interpret G': ParityGame "subgame V'" using subgame_ParityGame .
  fix v assume v: "v \<in> VV p" "\<not>deadend v"
  show "v \<rightarrow> ?\<sigma> v" proof (cases)
    assume "v \<in> V'"
    hence "v \<in> G'.VV p" using subgame_VV \<open>v \<in> VV p\<close> by blast
    moreover have "\<not>G'.deadend v" using G'_no_deadends \<open>v \<in> V'\<close> by blast
    ultimately have "v \<rightarrow>\<^bsub>subgame V'\<^esub> \<sigma>' v" using \<sigma>' unfolding G'.strategy_def by blast
    moreover have "\<sigma>' v = ?\<sigma> v" using \<open>v \<in> V'\<close> by simp
    ultimately show ?thesis by (metis subgame_E subsetCE)
  next
    assume "v \<notin> V'"
    thus ?thesis using v \<sigma> unfolding strategy_def by simp
  qed
qed

lemma valid_strategy_in_V: "\<lbrakk> strategy p \<sigma>; v \<in> VV p; \<not>deadend v \<rbrakk> \<Longrightarrow> \<sigma> v \<in> V"
  unfolding strategy_def using valid_edge_set by auto

lemma valid_strategy_only_in_V: "\<lbrakk> strategy p \<sigma>; \<And>v. v \<in> V \<Longrightarrow> \<sigma> v = \<sigma>' v \<rbrakk> \<Longrightarrow> strategy p \<sigma>'"
  unfolding strategy_def using edges_are_in_V(1) by auto

subsection \<open>Conforming Strategies\<close>

lemma path_conforms_with_strategy_ltl [intro]:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy p (ltl P) \<sigma>"
  by (drule path_conforms_with_strategy.cases) (simp_all add: path_conforms_with_strategy.intros(1))

lemma path_conforms_with_strategy_drop:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> path_conforms_with_strategy p (ldropn n P) \<sigma>"
  by (simp add: path_conforms_with_strategy_ltl ltl_ldrop[of "\<lambda>P. path_conforms_with_strategy p P \<sigma>"])

lemma path_conforms_with_strategy_prefix:
  "path_conforms_with_strategy p P \<sigma> \<Longrightarrow> lprefix P' P \<Longrightarrow> path_conforms_with_strategy p P' \<sigma>"
proof (coinduction arbitrary: P P')
  case (path_conforms_with_strategy P P')
  thus ?case proof (cases rule: path_conforms_with_strategy.cases)
    case path_conforms_LNil
    thus ?thesis using path_conforms_with_strategy(2) by auto
  next
    case path_conforms_LCons_LNil
    thus ?thesis by (metis lprefix_LCons_conv lprefix_antisym lprefix_code(1) path_conforms_with_strategy(2))
  next
    case (path_conforms_VVp v w)
    thus ?thesis proof (cases)
      assume "P' \<noteq> LNil \<and> P' \<noteq> LCons v LNil"
      hence "\<exists>Q. P' = LCons v (LCons w Q)"
        by (metis local.path_conforms_VVp(1) lprefix_LCons_conv path_conforms_with_strategy(2))
      thus ?thesis using local.path_conforms_VVp(1,3,4) path_conforms_with_strategy(2) by force
    qed auto
  next
    case (path_conforms_VVpstar v)
    thus ?thesis proof (cases)
      assume "P' \<noteq> LNil"
      hence "\<exists>Q. P' = LCons v Q"
        using local.path_conforms_VVpstar(1) lprefix_LCons_conv path_conforms_with_strategy(2) by fastforce
      thus ?thesis using local.path_conforms_VVpstar path_conforms_with_strategy(2) by auto
    qed simp
  qed
qed

lemma path_conforms_with_strategy_irrelevant:
  assumes "path_conforms_with_strategy p P \<sigma>" "v \<notin> lset P"
  shows "path_conforms_with_strategy p P (\<sigma>(v := w))"
  using assms apply (coinduction arbitrary: P) by (drule path_conforms_with_strategy.cases) auto

lemma path_conforms_with_strategy_irrelevant_deadend:
  assumes "path_conforms_with_strategy p P \<sigma>" "deadend v \<or> v \<notin> VV p" "valid_path P"
  shows "path_conforms_with_strategy p P (\<sigma>(v := w))"
using assms proof (coinduction arbitrary: P)
  let ?\<sigma> = "\<sigma>(v := w)"
  case (path_conforms_with_strategy P)
  thus ?case proof (cases rule: path_conforms_with_strategy.cases)
    case (path_conforms_VVp v' w Ps)
    have "w = ?\<sigma> v'" proof-
      from \<open>valid_path P\<close> have "\<not>deadend v'"
        using local.path_conforms_VVp(1) valid_path_cons_simp by blast
      with assms(2) have "v' \<noteq> v" using local.path_conforms_VVp(2) by blast
      thus "w = ?\<sigma> v'" by (simp add: local.path_conforms_VVp(3))
    qed
    moreover
      have "\<exists>P. LCons w Ps = P \<and> path_conforms_with_strategy p P \<sigma> \<and> (deadend v \<or> v \<notin> VV p) \<and> valid_path P"
    proof-
      have "valid_path (LCons w Ps)"
        using local.path_conforms_VVp(1) path_conforms_with_strategy(3) valid_path_ltl' by blast
      thus ?thesis using local.path_conforms_VVp(4) path_conforms_with_strategy(2) by blast
    qed
    ultimately show ?thesis using local.path_conforms_VVp(1,2) by blast
  next
    case (path_conforms_VVpstar v' Ps)
    have "\<exists>P. path_conforms_with_strategy p Ps \<sigma> \<and> (deadend v \<or> v \<notin> VV p) \<and> valid_path Ps"
      using local.path_conforms_VVpstar(1,3) path_conforms_with_strategy(2,3) valid_path_ltl' by blast
    thus ?thesis by (simp add: local.path_conforms_VVpstar(1,2))
  qed simp_all
qed

lemma path_conforms_with_strategy_irrelevant_updates:
  assumes "path_conforms_with_strategy p P \<sigma>" "\<And>v. v \<in> lset P \<Longrightarrow> \<sigma> v = \<sigma>' v"
  shows "path_conforms_with_strategy p P \<sigma>'"
using assms proof (coinduction arbitrary: P)
  case (path_conforms_with_strategy P)
  thus ?case proof (cases rule: path_conforms_with_strategy.cases)
    case (path_conforms_VVp v' w Ps)
    have "w = \<sigma>' v'" using local.path_conforms_VVp(1,3) path_conforms_with_strategy(2) by auto
    thus ?thesis using local.path_conforms_VVp(1,4) path_conforms_with_strategy(2) by auto
  qed simp_all
qed

lemma path_conforms_with_strategy_irrelevant':
  assumes "path_conforms_with_strategy p P (\<sigma>(v := w))" "v \<notin> lset P"
  shows "path_conforms_with_strategy p P \<sigma>"
  by (metis assms fun_upd_triv fun_upd_upd path_conforms_with_strategy_irrelevant)

lemma path_conforms_with_strategy_irrelevant_deadend':
  assumes "path_conforms_with_strategy p P (\<sigma>(v := w))" "deadend v \<or> v \<notin> VV p" "valid_path P"
  shows "path_conforms_with_strategy p P \<sigma>"
  by (metis assms fun_upd_triv fun_upd_upd path_conforms_with_strategy_irrelevant_deadend)

lemma path_conforms_with_strategy_start:
  "path_conforms_with_strategy p (LCons v (LCons w P)) \<sigma> \<Longrightarrow> v \<in> VV p \<Longrightarrow> \<sigma> v = w"
  by (drule path_conforms_with_strategy.cases) simp_all

lemma path_conforms_with_strategy_lappend:
  assumes
    P: "lfinite P" "\<not>lnull P" "path_conforms_with_strategy p P \<sigma>"
    and P': "\<not>lnull P'" "path_conforms_with_strategy p P' \<sigma>"
    and conforms: "llast P \<in> VV p \<Longrightarrow> \<sigma> (llast P) = lhd P'"
  shows "path_conforms_with_strategy p (lappend P P') \<sigma>"
using assms proof (induct P rule: lfinite_induct)
  case (LCons P)
  show ?case proof (cases)
    assume "lnull (ltl P)"
    then obtain v0 where v0: "P = LCons v0 LNil"
      by (metis LCons.prems(1) lhd_LCons_ltl llist.collapse(1))
    have "path_conforms_with_strategy p (LCons (lhd P) P') \<sigma>" proof (cases)
      assume "lhd P \<in> VV p"
      moreover with v0 have "lhd P' = \<sigma> (lhd P)"
        using LCons.prems(5) by auto
      ultimately show ?thesis
        using path_conforms_VVp[of "lhd P" p "lhd P'" \<sigma>]
        by (metis (no_types) LCons.prems(4) \<open>\<not>lnull P'\<close> lhd_LCons_ltl)
    next
      assume "lhd P \<notin> VV p"
      thus ?thesis using path_conforms_VVpstar using LCons.prems(4) v0 by blast
    qed
    thus ?thesis by (simp add: v0)
  next
    assume "\<not>lnull (ltl P)"
    hence *: "path_conforms_with_strategy p (lappend (ltl P) P') \<sigma>"
      by (metis LCons.hyps(3) LCons.prems(1) LCons.prems(2) LCons.prems(5) LCons.prems(5)
                assms(4) assms(5) lhd_LCons_ltl llast_LCons2 path_conforms_with_strategy_ltl)
    have "path_conforms_with_strategy p (LCons (lhd P) (lappend (ltl P) P')) \<sigma>" proof (cases)
      assume "lhd P \<in> VV p"
      moreover hence "lhd (ltl P) = \<sigma> (lhd P)"
        by (metis LCons.prems(1) LCons.prems(2) \<open>\<not>lnull (ltl P)\<close>
                  lhd_LCons_ltl path_conforms_with_strategy_start)
      ultimately show ?thesis
        using path_conforms_VVp[of "lhd P" p "lhd (ltl P)" \<sigma>] * \<open>\<not>lnull (ltl P)\<close>
        by (metis lappend_code(2) lhd_LCons_ltl)
    next
      assume "lhd P \<notin> VV p"
      thus ?thesis by (simp add: "*" path_conforms_VVpstar)
    qed
    with \<open>\<not>lnull P\<close> show "path_conforms_with_strategy p (lappend P P') \<sigma>"
      by (metis lappend_code(2) lhd_LCons_ltl)
  qed
qed simp

lemma path_conforms_with_strategy_VVpstar:
  assumes "lset P \<subseteq> VV p**"
  shows "path_conforms_with_strategy p P \<sigma>"
using assms proof (coinduction arbitrary: P)
  case (path_conforms_with_strategy P)
  moreover have "\<And>v Ps. P = LCons v Ps \<Longrightarrow> ?case" using path_conforms_with_strategy by auto
  ultimately show ?case by (cases "P = LNil", simp) (metis lnull_def not_lnull_conv)
qed

lemma subgame_path_conforms_with_strategy:
  assumes V': "V' \<subseteq> V" and P: "path_conforms_with_strategy p P \<sigma>" "lset P \<subseteq> V'"
  shows "ParityGame.path_conforms_with_strategy (subgame V') p P \<sigma>"
proof-
  have "lset P \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using P(2) V' by auto
  with P(1) show ?thesis
    by (coinduction arbitrary: P rule: ParityGame.path_conforms_with_strategy.coinduct[OF subgame_ParityGame])
       (cases rule: path_conforms_with_strategy.cases, auto)
qed

lemma (in vmc_path) subgame_path_vmc_path:
  assumes V': "V' \<subseteq> V" and P: "lset P \<subseteq> V'"
  shows "vmc_path (subgame V') P v0 p \<sigma>"
proof-
  interpret G': ParityGame "subgame V'" using subgame_ParityGame by blast
  show ?thesis proof
    show "G'.valid_path P" using subgame_valid_path P_valid P by blast
    show "G'.maximal_path P" using subgame_maximal_path V' P_maximal P by blast
    show "G'.path_conforms_with_strategy p P \<sigma>"
      using subgame_path_conforms_with_strategy V' P_conforms P by blast
  qed simp_all
qed

subsection \<open>Greedy Conforming Path\<close>

text \<open>
  Given a starting point and two strategies, there exists a path conforming to both strategies.
  Here we define this path.  Incidentally, this also shows that the assumptions of the locales
  \<open>vmc_path\<close> and \<open>vmc2_path\<close> are satisfiable.

  We are only interested in proving the existence of such a path, so the definition
  (i.e., the implementation) and most lemmas are private.
\<close>

context begin

private primcorec greedy_conforming_path :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a Path" where
  "greedy_conforming_path p \<sigma> \<sigma>' v0 =
    LCons v0 (if deadend v0
      then LNil
      else if v0 \<in> VV p
        then greedy_conforming_path p \<sigma> \<sigma>' (\<sigma> v0)
        else greedy_conforming_path p \<sigma> \<sigma>' (\<sigma>' v0))"

private lemma greedy_path_LNil: "greedy_conforming_path p \<sigma> \<sigma>' v0 \<noteq> LNil"
  using greedy_conforming_path.disc_iff llist.discI(1) by blast

private lemma greedy_path_lhd: "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P \<Longrightarrow> v = v0"
  using greedy_conforming_path.code by auto

private lemma greedy_path_deadend_v0: "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P \<Longrightarrow> P = LNil \<longleftrightarrow> deadend v0"
  by (metis (no_types, lifting) greedy_conforming_path.disc_iff
      greedy_conforming_path.simps(3) llist.disc(1) ltl_simps(2))

private corollary greedy_path_deadend_v:
  "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P \<Longrightarrow> P = LNil \<longleftrightarrow> deadend v"
  using greedy_path_deadend_v0 greedy_path_lhd by metis
corollary greedy_path_deadend_v': "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v LNil \<Longrightarrow> deadend v"
  using greedy_path_deadend_v by blast

private lemma greedy_path_ltl:
  assumes "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P"
  shows "P = LNil \<or> P = greedy_conforming_path p \<sigma> \<sigma>' (\<sigma> v0) \<or> P = greedy_conforming_path p \<sigma> \<sigma>' (\<sigma>' v0)"
  apply (insert assms, frule greedy_path_lhd)
  apply (cases "deadend v0", simp add: greedy_conforming_path.code)
  by (metis (no_types, lifting) greedy_conforming_path.sel(2) ltl_simps(2))

private lemma greedy_path_ltl_ex:
  assumes "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v P"
  shows "P = LNil \<or> (\<exists>v. P = greedy_conforming_path p \<sigma> \<sigma>' v)"
  using assms greedy_path_ltl by blast

private lemma greedy_path_ltl_VVp:
  assumes "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v0 P" "v0 \<in> VV p" "\<not>deadend v0"
  shows "\<sigma> v0 = lhd P"
  using assms greedy_conforming_path.code by auto

private lemma greedy_path_ltl_VVpstar:
  assumes "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v0 P" "v0 \<in> VV p**" "\<not>deadend v0"
  shows "\<sigma>' v0 = lhd P"
  using assms greedy_conforming_path.code by auto

private lemma greedy_conforming_path_properties:
  assumes "v0 \<in> V" "strategy p \<sigma>" "strategy p** \<sigma>'"
  shows
        greedy_path_not_null:  "\<not>lnull (greedy_conforming_path p \<sigma> \<sigma>' v0)"
    and greedy_path_v0:        "greedy_conforming_path p \<sigma> \<sigma>' v0 $ 0 = v0"
    and greedy_path_valid:     "valid_path (greedy_conforming_path p \<sigma> \<sigma>' v0)"
    and greedy_path_maximal:   "maximal_path (greedy_conforming_path p \<sigma> \<sigma>' v0)"
    and greedy_path_conforms:  "path_conforms_with_strategy p (greedy_conforming_path p \<sigma> \<sigma>' v0) \<sigma>"
    and greedy_path_conforms': "path_conforms_with_strategy p** (greedy_conforming_path p \<sigma> \<sigma>' v0) \<sigma>'"
proof-
  define P where [simp]: "P = greedy_conforming_path p \<sigma> \<sigma>' v0"

  show "\<not>lnull P" "P $ 0 = v0" by (simp_all add: lnth_0_conv_lhd)

  {
    fix v0 assume "v0 \<in> V"
    let ?P = "greedy_conforming_path p \<sigma> \<sigma>' v0"
    assume asm: "\<not>(\<exists>v. ?P = LCons v LNil)"
    obtain P' where P': "?P = LCons v0 P'" by (metis greedy_path_LNil greedy_path_lhd neq_LNil_conv)
    hence "\<not>deadend v0" using asm greedy_path_deadend_v0 \<open>v0 \<in> V\<close> by blast
    from P' have 1: "\<not>lnull P'" using asm llist.collapse(1) \<open>v0 \<in> V\<close> greedy_path_deadend_v0 by blast
    moreover from P' \<open>\<not>deadend v0\<close> assms(2,3) \<open>v0 \<in> V\<close>
      have "v0\<rightarrow>lhd P'"
      unfolding strategy_def using greedy_path_ltl_VVp greedy_path_ltl_VVpstar
      by (cases "v0 \<in> VV p") auto
    moreover hence "lhd P' \<in> V" by blast
    moreover hence "\<exists>v. P' = greedy_conforming_path p \<sigma> \<sigma>' v \<and> v \<in> V"
      by (metis P' calculation(1) greedy_conforming_path.simps(2) greedy_path_ltl_ex lnull_def)
    text \<open>The conjunction of all the above.\<close>
    ultimately
      have "\<exists>P'. ?P = LCons v0 P' \<and> \<not>lnull P' \<and> v0\<rightarrow>lhd P' \<and> lhd P' \<in> V
        \<and> (\<exists>v. P' = greedy_conforming_path p \<sigma> \<sigma>' v \<and> v \<in> V)"
      using P' by blast
  } note coinduction_helper = this

  show "valid_path P" using assms unfolding P_def
  proof (coinduction arbitrary: v0 rule: valid_path.coinduct)
    case (valid_path v0)
    from \<open>v0 \<in> V\<close> assms(2,3) show ?case
      using coinduction_helper[of v0] greedy_path_lhd by blast
  qed

  show "maximal_path P" using assms unfolding P_def
  proof (coinduction arbitrary: v0)
    case (maximal_path v0)
    from \<open>v0 \<in> V\<close> assms(2,3) show ?case
      using coinduction_helper[of v0] greedy_path_deadend_v' by blast
  qed

  {
    fix p'' \<sigma>'' assume p'': "(p'' = p \<and> \<sigma>'' = \<sigma>) \<or> (p'' = p** \<and> \<sigma>'' = \<sigma>')"
    moreover with assms have "strategy p'' \<sigma>''" by blast
    hence "path_conforms_with_strategy p'' P \<sigma>''" using \<open>v0 \<in> V\<close> unfolding P_def
    proof (coinduction arbitrary: v0)
      case (path_conforms_with_strategy v0)
      show ?case proof (cases "v0 \<in> VV p''")
        case True
        { assume "\<not>(\<exists>v. greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v LNil)"
          with \<open>v0 \<in> V\<close> obtain P' where
            P': "greedy_conforming_path p \<sigma> \<sigma>' v0 = LCons v0 P'" "\<not>lnull P'" "v0\<rightarrow>lhd P'"
                "lhd P' \<in> V" "\<exists>v. P' = greedy_conforming_path p \<sigma> \<sigma>' v \<and> v \<in> V"
            using coinduction_helper by blast
          with \<open>v0 \<in> VV p''\<close> p'' have "\<sigma>'' v0 = lhd P'"
            using greedy_path_ltl_VVp greedy_path_ltl_VVpstar by blast
          with \<open>v0 \<in> VV p''\<close> P'(1,2,5) have ?path_conforms_VVp
            using greedy_conforming_path.code path_conforms_with_strategy(1) by fastforce
        }
        thus ?thesis by auto
      next
        case False
        thus ?thesis using coinduction_helper[of v0] path_conforms_with_strategy by auto
      qed
    qed
  }
  thus "path_conforms_with_strategy p P \<sigma>" "path_conforms_with_strategy p** P \<sigma>'" by blast+
qed

corollary strategy_conforming_path_exists:
  assumes "v0 \<in> V" "strategy p \<sigma>" "strategy p** \<sigma>'"
  obtains P where "vmc2_path G P v0 p \<sigma> \<sigma>'"
proof
  show "vmc2_path G (greedy_conforming_path p \<sigma> \<sigma>' v0) v0 p \<sigma> \<sigma>'"
    using assms by unfold_locales (simp_all add: greedy_conforming_path_properties)
qed

corollary strategy_conforming_path_exists_single:
  assumes "v0 \<in> V" "strategy p \<sigma>"
  obtains P where "vmc_path G P v0 p \<sigma>"
proof
  show "vmc_path G (greedy_conforming_path p \<sigma> \<sigma>_arbitrary v0) v0 p \<sigma>"
    using assms by unfold_locales (simp_all add: greedy_conforming_path_properties)
qed

end

end

subsection \<open>Valid Maximal Conforming Paths\<close>

text \<open>Now is the time to add some lemmas to the locale \<open>vmc_path\<close>.\<close>

context vmc_path begin
lemma Ptl_conforms [simp]: "path_conforms_with_strategy p (ltl P) \<sigma>"
  using P_conforms path_conforms_with_strategy_ltl by blast
lemma Pdrop_conforms [simp]: "path_conforms_with_strategy p (ldropn n P) \<sigma>"
  using P_conforms path_conforms_with_strategy_drop by blast
lemma prefix_conforms [simp]: "path_conforms_with_strategy p (ltake n P) \<sigma>"
  using P_conforms path_conforms_with_strategy_prefix by blast
lemma extension_conforms [simp]:
  "(v' \<in> VV p \<Longrightarrow> \<sigma> v' = v0) \<Longrightarrow> path_conforms_with_strategy p (LCons v' P) \<sigma>"
  by (metis P_LCons P_conforms path_conforms_VVp path_conforms_VVpstar)

lemma extension_valid_maximal_conforming:
  assumes "v'\<rightarrow>v0" "v' \<in> VV p \<Longrightarrow> \<sigma> v' = v0"
  shows "vmc_path G (LCons v' P) v' p \<sigma>"
  using assms by unfold_locales simp_all

lemma vmc_path_ldropn:
  assumes "enat n < llength P"
  shows "vmc_path G (ldropn n P) (P $ n) p \<sigma>"
  using assms by unfold_locales (simp_all add: lhd_ldropn)

lemma conforms_to_another_strategy:
  "path_conforms_with_strategy p P \<sigma>' \<Longrightarrow> vmc_path G P v0 p \<sigma>'"
  using P_not_null P_valid P_maximal P_v0 by unfold_locales blast+
end

lemma (in ParityGame) valid_maximal_conforming_path_0:
  assumes "\<not>lnull P" "valid_path P" "maximal_path P" "path_conforms_with_strategy p P \<sigma>"
  shows "vmc_path G P (P $ 0) p \<sigma>"
  using assms by unfold_locales (simp_all add: lnth_0_conv_lhd)

subsection \<open>Valid Maximal Conforming Paths with One Edge\<close>

text \<open>
  We define a locale for valid maximal conforming paths that contain at least one edge.
  This is equivalent to the first node being no deadend.  This assumption allows us to prove
  much stronger lemmas about @{term "ltl P"} compared to @{term "vmc_path"}.
\<close>

locale vmc_path_no_deadend = vmc_path +
  assumes v0_no_deadend [simp]: "\<not>deadend v0"
begin
definition "w0 \<equiv> lhd (ltl P)"

lemma Ptl_not_null [simp]: "\<not>lnull (ltl P)"
  using P_LCons P_maximal maximal_no_deadend v0_no_deadend by metis
lemma Ptl_LCons: "ltl P = LCons w0 (ltl (ltl P))" unfolding w0_def by simp
lemma P_LCons': "P = LCons v0 (LCons w0 (ltl (ltl P)))" using P_LCons Ptl_LCons by simp
lemma v0_edge_w0 [simp]: "v0\<rightarrow>w0" using P_valid P_LCons' by (metis valid_path_edges')

lemma Ptl_0: "ltl P $ 0 = lhd (ltl P)" by (simp add: lhd_conv_lnth)
lemma P_Suc_0: "P $ Suc 0 = w0" by (simp add: P_lnth_Suc Ptl_0 w0_def)
lemma Ptl_edge [simp]: "v0 \<rightarrow> lhd (ltl P)" by (metis P_LCons' P_valid valid_path_edges' w0_def)

lemma v0_conforms: "v0 \<in> VV p \<Longrightarrow> \<sigma> v0 = w0"
  using path_conforms_with_strategy_start by (metis P_LCons' P_conforms)

lemma w0_V [simp]: "w0 \<in> V" by (metis Ptl_LCons Ptl_valid valid_path_cons_simp)
lemma w0_lset_P [simp]: "w0 \<in> lset P" by (metis P_LCons' lset_intros(1) lset_intros(2))

lemma vmc_path_ltl [simp]: "vmc_path G (ltl P) w0 p \<sigma>" by (unfold_locales) (simp_all add: w0_def)
end

context vmc_path begin

lemma vmc_path_lnull_ltl_no_deadend:
  "\<not>lnull (ltl P) \<Longrightarrow> vmc_path_no_deadend G P v0 p \<sigma>"
  using P_0 P_no_deadends by (unfold_locales) (metis enat_ltl_Suc lnull_0_llength)

lemma vmc_path_conforms:
  assumes "enat (Suc n) < llength P" "P $ n \<in> VV p"
  shows "\<sigma> (P $ n) = P $ Suc n"
proof-
  define P' where "P' = ldropn n P"
  then interpret P': vmc_path G P' "P $ n" p \<sigma> using vmc_path_ldropn assms(1) Suc_llength by blast
  have "\<not>deadend (P $ n)" using assms(1) P_no_deadends by blast
  then interpret P': vmc_path_no_deadend G P' "P $ n" p \<sigma> by unfold_locales
  have "\<sigma> (P $ n) = P'.w0" using P'.v0_conforms assms(2) by blast
  thus ?thesis using P'_def P'.P_Suc_0 assms(1) by simp
qed

subsection \<open>@{term lset} Induction Schemas for Paths\<close>

text \<open>Let us define an induction schema useful for proving @{term "lset P \<subseteq> S"}.\<close>

lemma vmc_path_lset_induction [consumes 1, case_names base step]:
  assumes "Q P"
    and base: "v0 \<in> S"
    and step_assumption: "\<And>P v0. \<lbrakk> vmc_path_no_deadend G P v0 p \<sigma>; v0 \<in> S; Q P \<rbrakk>
      \<Longrightarrow> Q (ltl P) \<and> (vmc_path_no_deadend.w0 P) \<in> S"
  shows "lset P \<subseteq> S"
proof
  fix v assume "v \<in> lset P"
  thus "v \<in> S" using vmc_path_axioms assms(1,2) proof (induct arbitrary: v0 rule: llist_set_induct)
    case (find P)
    then interpret vmc_path G P v0 p \<sigma> by blast
    show ?case by (simp add: find.prems(3))
  next
    case (step P v)
    then interpret vmc_path G P v0 p \<sigma> by blast
    show ?case proof (cases)
      assume "lnull (ltl P)"
      hence "P = LCons v LNil" by (metis llist.disc(2) lset_cases step.hyps(2))
      thus ?thesis using step.prems(3) P_LCons by blast
    next
      assume "\<not>lnull (ltl P)"
      then interpret vmc_path_no_deadend G P v0 p \<sigma>
        using vmc_path_lnull_ltl_no_deadend by blast
      show "v \<in> S"
        using step.hyps(3)
              step_assumption[OF vmc_path_no_deadend_axioms \<open>v0 \<in> S\<close> \<open>Q P\<close>]
              vmc_path_ltl
        by blast
    qed
  qed
qed

text \<open>@{thm vmc_path_lset_induction} without the Q predicate.\<close>
corollary vmc_path_lset_induction_simple [case_names base step]:
  assumes base: "v0 \<in> S"
    and step: "\<And>P v0. \<lbrakk> vmc_path_no_deadend G P v0 p \<sigma>; v0 \<in> S \<rbrakk>
      \<Longrightarrow> vmc_path_no_deadend.w0 P \<in> S"
  shows "lset P \<subseteq> S"
  using assms vmc_path_lset_induction[of "\<lambda>P. True"] by blast

text \<open>Another induction schema for proving @{term "lset P \<subseteq> S"} based on closure properties.\<close>

lemma vmc_path_lset_induction_closed_subset [case_names VVp VVpstar v0 disjoint]:
  assumes VVp: "\<And>v. \<lbrakk> v \<in> S; \<not>deadend v; v \<in> VV p \<rbrakk> \<Longrightarrow> \<sigma> v \<in> S \<union> T"
    and VVpstar: "\<And>v w. \<lbrakk> v \<in> S; \<not>deadend v; v \<in> VV p** ; v\<rightarrow>w \<rbrakk> \<Longrightarrow> w \<in> S \<union> T"
    and v0: "v0 \<in> S"
    and disjoint: "lset P \<inter> T = {}"
  shows "lset P \<subseteq> S"
using disjoint proof (induct rule: vmc_path_lset_induction)
  case (step P v0)
  interpret vmc_path_no_deadend G P v0 p \<sigma> using step.hyps(1) .
  have "lset (ltl P) \<inter> T = {}" using step.hyps(3)
    by (meson disjoint_eq_subset_Compl lset_ltl order.trans)
  moreover have "w0 \<in> S \<union> T"
    using assms(1,2)[of v0] step.hyps(2) v0_no_deadend v0_conforms
    by (cases "v0 \<in> VV p") simp_all
  ultimately show ?case using step.hyps(3) w0_lset_P by blast
qed (insert v0)

end

end
