section \<open>Parity Games\<close>

theory ParityGame
imports
  Main
  MoreCoinductiveList
begin

subsection \<open>Basic definitions\<close>

text \<open>@{typ "'a"} is the node type.  Edges are pairs of nodes.\<close>
type_synonym 'a Edge = "'a \<times> 'a"

text \<open>A path is a possibly infinite list of nodes.\<close>
type_synonym 'a Path = "'a llist"

subsection \<open>Graphs\<close>

text \<open>
  We define graphs as a locale over a record.
  The record contains nodes (AKA vertices) and edges.
  The locale adds the assumption that the edges are pairs of nodes.
\<close>

record 'a Graph =
  verts :: "'a set" ("V\<index>")
  arcs :: "'a Edge set" ("E\<index>")
abbreviation is_arc :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<index>" 60) where
  "v \<rightarrow>\<^bsub>G\<^esub> w \<equiv> (v,w) \<in> E\<^bsub>G\<^esub>"

locale Digraph =
  fixes G (structure)
  assumes valid_edge_set: "E \<subseteq> V \<times> V"
begin
lemma edges_are_in_V [intro]: "v\<rightarrow>w \<Longrightarrow> v \<in> V" "v\<rightarrow>w \<Longrightarrow> w \<in> V" using valid_edge_set by blast+

text \<open>A node without successors is a \emph{deadend}.\<close>
abbreviation deadend :: "'a \<Rightarrow> bool" where "deadend v \<equiv> \<not>(\<exists>w \<in> V. v \<rightarrow> w)"

subsection \<open>Valid Paths\<close>

text \<open>
  We say that a path is \emph{valid} if it is empty or if it starts in @{term V} and walks along edges.
\<close>
coinductive valid_path :: "'a Path \<Rightarrow> bool" where
  valid_path_base: "valid_path LNil"
| valid_path_base': "v \<in> V \<Longrightarrow> valid_path (LCons v LNil)"
| valid_path_cons: "\<lbrakk> v \<in> V; w \<in> V; v\<rightarrow>w; valid_path Ps; \<not>lnull Ps; lhd Ps = w \<rbrakk>
    \<Longrightarrow> valid_path (LCons v Ps)"

inductive_simps valid_path_cons_simp: "valid_path (LCons x xs)"

lemma valid_path_ltl': "valid_path (LCons v Ps) \<Longrightarrow> valid_path Ps"
  using valid_path.simps by blast
lemma valid_path_ltl: "valid_path P \<Longrightarrow> valid_path (ltl P)"
  by (metis llist.exhaust_sel ltl_simps(1) valid_path_ltl')
lemma valid_path_drop: "valid_path P \<Longrightarrow> valid_path (ldropn n P)"
  by (simp add: valid_path_ltl ltl_ldrop)

lemma valid_path_in_V: assumes "valid_path P" shows "lset P \<subseteq> V" proof
  fix x assume "x \<in> lset P" thus "x \<in> V"
    using assms by (induct rule: llist.set_induct) (auto intro: valid_path.cases)
qed
lemma valid_path_finite_in_V: "\<lbrakk> valid_path P; enat n < llength P \<rbrakk> \<Longrightarrow> P $ n \<in> V"
  using valid_path_in_V lset_lnth_member by blast

lemma valid_path_edges': "valid_path (LCons v (LCons w Ps)) \<Longrightarrow> v\<rightarrow>w"
  using valid_path.cases by fastforce
lemma valid_path_edges:
  assumes "valid_path P" "enat (Suc n) < llength P"
  shows "P $ n \<rightarrow> P $ Suc n"
proof-
  define P' where "P' = ldropn n P"
  have "enat n < llength P" using assms(2) enat_ord_simps(2) less_trans by blast
  hence "P' $ 0 = P $ n" by (simp add: P'_def)
  moreover have "P' $ Suc 0 = P $ Suc n"
    by (metis One_nat_def P'_def Suc_eq_plus1 add.commute assms(2) lnth_ldropn)
  ultimately have "\<exists>Ps. P' = LCons (P $ n) (LCons (P $ Suc n) Ps)"
    by (metis P'_def \<open>enat n < llength P\<close> assms(2) ldropn_Suc_conv_ldropn)
  moreover have "valid_path P'" by (simp add: P'_def assms(1) valid_path_drop)
  ultimately show ?thesis using valid_path_edges' by blast
qed

lemma valid_path_coinduct [consumes 1, case_names base step, coinduct pred: valid_path]:
  assumes major: "Q P"
    and base: "\<And>v P. Q (LCons v LNil) \<Longrightarrow> v \<in> V"
    and step: "\<And>v w P. Q (LCons v (LCons w P)) \<Longrightarrow> v\<rightarrow>w \<and> (Q (LCons w P) \<or> valid_path (LCons w P))"
  shows "valid_path P"
using major proof (coinduction arbitrary: P)
  case valid_path
  { assume "P \<noteq> LNil" "\<not>(\<exists>v. P = LCons v LNil \<and> v \<in> V)"
    then obtain v w P' where "P = LCons v (LCons w P')"
      using neq_LNil_conv base valid_path by metis
    hence ?case using step valid_path by auto
  }
  thus ?case by blast
qed

lemma valid_path_no_deadends:
  "\<lbrakk> valid_path P; enat (Suc i) < llength P \<rbrakk> \<Longrightarrow> \<not>deadend (P $ i)"
  using valid_path_edges by blast

lemma valid_path_ends_on_deadend:
  "\<lbrakk> valid_path P; enat i < llength P; deadend (P $ i) \<rbrakk> \<Longrightarrow> enat (Suc i) = llength P"
  using valid_path_no_deadends by (metis enat_iless enat_ord_simps(2) neq_iff not_less_eq)

lemma valid_path_prefix: "\<lbrakk> valid_path P; lprefix P' P \<rbrakk> \<Longrightarrow> valid_path P'"
proof (coinduction arbitrary: P' P)
  case (step v w P'' P' P)
  then obtain Ps where Ps: "LCons v (LCons w Ps) = P" by (metis LCons_lprefix_conv)
  hence "valid_path (LCons w Ps)" using valid_path_ltl' step(2) by blast
  moreover have "lprefix (LCons w P'') (LCons w Ps)" using Ps step(1,3) by auto
  ultimately show ?case using Ps step(2) valid_path_edges' by blast
qed (metis LCons_lprefix_conv valid_path_cons_simp)

lemma valid_path_lappend:
  assumes "valid_path P" "valid_path P'" "\<lbrakk> \<not>lnull P; \<not>lnull P' \<rbrakk> \<Longrightarrow> llast P\<rightarrow>lhd P'"
  shows "valid_path (lappend P P')"
proof (cases, cases)
  assume "\<not>lnull P" "\<not>lnull P'"
  thus ?thesis using assms proof (coinduction arbitrary: P' P)
    case (step v w P'' P' P)
    show ?case proof (cases)
      assume "lnull (ltl P)"
      thus ?case using step(1,2,3,5,6)
        by (metis lhd_LCons lhd_LCons_ltl lhd_lappend llast_singleton
                  llist.collapse(1) ltl_lappend ltl_simps(2))
    next
      assume "\<not>lnull (ltl P)"
      moreover have "ltl (lappend P P') = lappend (ltl P) P'" using step(2) by simp
      ultimately show ?case using step
        by (metis (no_types, lifting)
            lhd_LCons lhd_LCons_ltl lhd_lappend llast_LCons ltl_simps(2)
            valid_path_edges' valid_path_ltl)
    qed
  qed (metis llist.disc(1) lnull_lappend ltl_lappend ltl_simps(2))
qed (simp_all add: assms(1,2) lappend_lnull1 lappend_lnull2)

text \<open>A valid path is still valid in a supergame.\<close>
lemma valid_path_supergame:
  assumes "valid_path P" and G': "Digraph G'" "V \<subseteq> V\<^bsub>G'\<^esub>" "E \<subseteq> E\<^bsub>G'\<^esub>"
  shows "Digraph.valid_path G' P"
using \<open>valid_path P\<close> proof (coinduction arbitrary: P
  rule: Digraph.valid_path_coinduct[OF G'(1), case_names base step])
  case base thus ?case using G'(2) valid_path_cons_simp by auto
qed (meson G'(3) subset_eq valid_path_edges' valid_path_ltl')

subsection \<open>Maximal Paths\<close>

text \<open>
  We say that a path is \emph{maximal} if it is empty or if it ends in a deadend.
\<close>
coinductive maximal_path where
  maximal_path_base: "maximal_path LNil"
| maximal_path_base': "deadend v \<Longrightarrow> maximal_path (LCons v LNil)"
| maximal_path_cons: "\<not>lnull Ps \<Longrightarrow> maximal_path Ps \<Longrightarrow> maximal_path (LCons v Ps)"

lemma maximal_no_deadend: "maximal_path (LCons v Ps) \<Longrightarrow> \<not>deadend v \<Longrightarrow> \<not>lnull Ps"
  by (metis lhd_LCons llist.distinct(1) ltl_simps(2) maximal_path.simps)
lemma maximal_ltl: "maximal_path P \<Longrightarrow> maximal_path (ltl P)"
  by (metis ltl_simps(1) ltl_simps(2) maximal_path.simps)
lemma maximal_drop: "maximal_path P \<Longrightarrow> maximal_path (ldropn n P)"
  by (simp add: maximal_ltl ltl_ldrop)

lemma maximal_path_lappend:
  assumes "\<not>lnull P'" "maximal_path P'"
  shows "maximal_path (lappend P P')"
proof (cases)
  assume "\<not>lnull P"
  thus ?thesis using assms proof (coinduction arbitrary: P' P rule: maximal_path.coinduct)
    case (maximal_path P' P)
    let ?P = "lappend P P'"
    show ?case proof (cases "?P = LNil \<or> (\<exists>v. ?P = LCons v LNil \<and> deadend v)")
      case False
      then obtain Ps v where P: "?P = LCons v Ps" by (meson neq_LNil_conv)
      hence "Ps = lappend (ltl P) P'" by (simp add: lappend_ltl maximal_path(1))
      hence "\<exists>Ps1 P'. Ps = lappend Ps1 P' \<and> \<not>lnull P' \<and> maximal_path P'"
        using maximal_path(2) maximal_path(3) by auto
      thus ?thesis using P lappend_lnull1 by fastforce
    qed blast
  qed
qed (simp add: assms(2) lappend_lnull1[of P P'])

lemma maximal_ends_on_deadend:
  assumes "maximal_path P" "lfinite P" "\<not>lnull P"
  shows "deadend (llast P)"
proof-
  from \<open>lfinite P\<close> \<open>\<not>lnull P\<close> obtain n where n: "llength P = enat (Suc n)"
    by (metis enat_ord_simps(2) gr0_implies_Suc lfinite_llength_enat lnull_0_llength)
  define P' where "P' = ldropn n P"
  hence "maximal_path P'" using assms(1) maximal_drop by blast
  thus ?thesis proof (cases rule: maximal_path.cases)
    case (maximal_path_base' v)
    hence "deadend (llast P')" unfolding P'_def by simp
    thus ?thesis unfolding P'_def using llast_ldropn[of n P] n
      by (metis P'_def ldropn_eq_LConsD local.maximal_path_base'(1))
  next
    case (maximal_path_cons P'' v)
    hence "ldropn (Suc n) P = P''" unfolding P'_def by (metis ldrop_eSuc_ltl ltl_ldropn ltl_simps(2))
    thus ?thesis using n maximal_path_cons(2) by auto
  qed (simp add: P'_def n ldropn_eq_LNil)
qed

lemma maximal_ends_on_deadend': "\<lbrakk> lfinite P; deadend (llast P) \<rbrakk> \<Longrightarrow> maximal_path P"
proof (coinduction arbitrary: P rule: maximal_path.coinduct)
  case (maximal_path P)
  show ?case proof (cases)
    assume "P \<noteq> LNil"
    then obtain v P' where P': "P = LCons v P'" by (meson neq_LNil_conv)
    show ?thesis proof (cases)
      assume "P' = LNil" thus ?thesis using P' maximal_path(2) by auto
    qed (metis P' lfinite_LCons llast_LCons llist.collapse(1) maximal_path(1,2))
  qed simp
qed

lemma infinite_path_is_maximal: "\<lbrakk> valid_path P; \<not>lfinite P \<rbrakk> \<Longrightarrow> maximal_path P"
  by (coinduction arbitrary: P rule: maximal_path.coinduct)
     (cases rule: valid_path.cases, auto)

end \<comment> \<open>locale Digraph\<close>

subsection \<open>Parity Games\<close>

text \<open>Parity games are games played by two players, called \Even and \Odd.\<close>

datatype Player = Even | Odd

abbreviation "other_player p \<equiv> (if p = Even then Odd else Even)"
notation other_player ("(_**)" [1000] 1000)
lemma other_other_player [simp]: "p**** = p" using Player.exhaust by auto

text \<open>
  A parity game is tuple $(V,E,V_0,\omega)$, where $(V,E)$ is a graph, $V_0 \subseteq V$
  and @{term \<omega>} is a function from $V \to \mathbb{N}$ with finite image.
\<close>

record 'a ParityGame = "'a Graph" +
  player0 :: "'a set" ("V0\<index>")
  priority :: "'a \<Rightarrow> nat" ("\<omega>\<index>")

locale ParityGame = Digraph G for G :: "('a, 'b) ParityGame_scheme" (structure) +
  assumes valid_player0_set: "V0 \<subseteq> V"
    and priorities_finite: "finite (\<omega> ` V)"
begin
text \<open>\<open>VV p\<close> is the set of nodes belonging to player @{term p}.\<close>
abbreviation VV :: "Player \<Rightarrow> 'a set" where "VV p \<equiv> (if p = Even then V0 else V - V0)"
lemma VVp_to_V [intro]: "v \<in> VV p \<Longrightarrow> v \<in> V" using valid_player0_set by (cases p) auto
lemma VV_impl1: "v \<in> VV p \<Longrightarrow> v \<notin> VV p**" by auto
lemma VV_impl2: "v \<in> VV p** \<Longrightarrow> v \<notin> VV p" by auto
lemma VV_equivalence [iff]: "v \<in> V \<Longrightarrow> v \<notin> VV p \<longleftrightarrow> v \<in> VV p**" by auto
lemma VV_cases [consumes 1]: "\<lbrakk> v \<in> V ; v \<in> VV p \<Longrightarrow> P ; v \<in> VV p** \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" by auto

subsection \<open>Sets of Deadends\<close>

definition "deadends p \<equiv> {v \<in> VV p. deadend v}"
lemma deadends_in_V: "deadends p \<subseteq> V" unfolding deadends_def by blast

subsection \<open>Subgames\<close>

text \<open>We define a subgame by restricting the set of nodes to a given subset.\<close>

definition subgame where
  "subgame V' \<equiv> G\<lparr>
    verts   := V \<inter> V',
    arcs    := E \<inter> (V' \<times> V'),
    player0 := V0 \<inter> V' \<rparr>"

lemma subgame_V [simp]: "V\<^bsub>subgame V'\<^esub> \<subseteq> V"
  and subgame_E [simp]: "E\<^bsub>subgame V'\<^esub> \<subseteq> E"
  and subgame_\<omega>: "\<omega>\<^bsub>subgame V'\<^esub> = \<omega>"
  unfolding subgame_def by simp_all

lemma
  assumes "V' \<subseteq> V"
  shows subgame_V' [simp]: "V\<^bsub>subgame V'\<^esub> = V'"
    and subgame_E' [simp]: "E\<^bsub>subgame V'\<^esub> = E \<inter> (V\<^bsub>subgame V'\<^esub> \<times> V\<^bsub>subgame V'\<^esub>)"
  unfolding subgame_def using assms by auto

lemma subgame_VV [simp]: "ParityGame.VV (subgame V') p = V' \<inter> VV p" proof-
  have "ParityGame.VV (subgame V') Even = V' \<inter> VV Even" unfolding subgame_def by auto
  moreover have "ParityGame.VV (subgame V') Odd = V' \<inter> VV Odd" proof-
    have "V' \<inter> V - (V0 \<inter> V') = V' \<inter> V \<inter> (V - V0)" by blast
    thus ?thesis unfolding subgame_def by auto
  qed
  ultimately show ?thesis by simp
qed
corollary subgame_VV_subset [simp]: "ParityGame.VV (subgame V') p \<subseteq> VV p" by simp

lemma subgame_finite [simp]: "finite (\<omega>\<^bsub>subgame V'\<^esub> ` V\<^bsub>subgame V'\<^esub>)" proof-
  have "finite (\<omega> ` V\<^bsub>subgame V'\<^esub>)" using subgame_V priorities_finite
    by (meson finite_subset image_mono)
  thus ?thesis by (simp add: subgame_def)
qed

lemma subgame_\<omega>_subset [simp]: "\<omega>\<^bsub>subgame V'\<^esub> ` V\<^bsub>subgame V'\<^esub> \<subseteq> \<omega> ` V"
  by (simp add: image_mono subgame_\<omega>)

lemma subgame_Digraph: "Digraph (subgame V')"
  by (unfold_locales) (auto simp add: subgame_def)

lemma subgame_ParityGame:
  shows "ParityGame (subgame V')"
proof (unfold_locales)
  show "E\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub> \<times> V\<^bsub>subgame V'\<^esub>"
    using subgame_Digraph[unfolded Digraph_def] .
  show "V0\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using valid_player0_set by auto
  show "finite (\<omega>\<^bsub>subgame V'\<^esub> ` V\<^bsub>subgame V'\<^esub>)" by simp
qed

lemma subgame_valid_path:
  assumes P: "valid_path P" "lset P \<subseteq> V'"
  shows "Digraph.valid_path (subgame V') P"
proof-
  have "lset P \<subseteq> V" using P(1) valid_path_in_V by blast
  hence "lset P \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using P(2) by auto
  with P(1) show ?thesis
  proof (coinduction arbitrary: P
    rule: Digraph.valid_path.coinduct[OF subgame_Digraph, case_names IH])
    case IH
    thus ?case proof (cases rule: valid_path.cases)
      case (valid_path_cons v w Ps)
      moreover hence "v \<in> V\<^bsub>subgame V'\<^esub>" "w \<in> V\<^bsub>subgame V'\<^esub>" using IH(2) by auto
      moreover hence "v \<rightarrow>\<^bsub>subgame V'\<^esub> w" using local.valid_path_cons(4) subgame_def by auto
      moreover have "valid_path Ps" using IH(1) valid_path_ltl' local.valid_path_cons(1) by blast
      ultimately show ?thesis using IH(2) by auto
    qed auto
  qed
qed

lemma subgame_maximal_path:
  assumes V': "V' \<subseteq> V" and P: "maximal_path P" "lset P \<subseteq> V'"
  shows "Digraph.maximal_path (subgame V') P"
proof-
  have "lset P \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using P(2) V' by auto
  with P(1) V' show ?thesis
    by (coinduction arbitrary: P rule: Digraph.maximal_path.coinduct[OF subgame_Digraph])
       (cases rule: maximal_path.cases, auto)
qed

subsection \<open>Priorities Occurring Infinitely Often\<close>

text \<open>
  The set of priorities that occur infinitely often on a given path.  We need this to define the
  winning condition of parity games.
\<close>
definition path_inf_priorities :: "'a Path \<Rightarrow> nat set" where
  "path_inf_priorities P \<equiv> {k. \<forall>n. k \<in> lset (ldropn n (lmap \<omega> P))}"

text \<open>
  Because @{term \<omega>} is image-finite, by the pigeon-hole principle every infinite path has at least
  one priority that occurs infinitely often.
\<close>
lemma path_inf_priorities_is_nonempty:
  assumes P: "valid_path P" "\<not>lfinite P"
  shows "\<exists>k. k \<in> path_inf_priorities P"
proof-
  text \<open>Define a map from indices to priorities on the path.\<close>
  define f where "f i = \<omega> (P $ i)" for i
  have "range f \<subseteq> \<omega> ` V" unfolding f_def
    using valid_path_in_V[OF P(1)] lset_nth_member_inf[OF P(2)]
    by blast
  hence "finite (range f)"
    using priorities_finite finite_subset by blast
  then obtain n0 where n0: "\<not>(finite {n. f n = f n0})"
    using pigeonhole_infinite[of UNIV f] by auto
  define k where "k = f n0"
  text \<open>The priority @{term k} occurs infinitely often.\<close>
  have "lmap \<omega> P $ n0 = k" unfolding f_def k_def
    using assms(2) by (simp add: infinite_small_llength)
  moreover {
    fix n assume "lmap \<omega> P $ n = k"
    have "\<exists>n' > n. f n' = k" unfolding k_def using n0 infinite_nat_iff_unbounded by auto
    hence "\<exists>n' > n. lmap \<omega> P $ n' = k" unfolding f_def
      using assms(2) by (simp add: infinite_small_llength)
  }
  ultimately have "\<forall>n. k \<in> lset (ldropn n (lmap \<omega> P))"
    using index_infinite_set[of "lmap \<omega> P" n0 k] P(2) lfinite_lmap
    by blast
  thus ?thesis unfolding path_inf_priorities_def by blast
qed

lemma path_inf_priorities_at_least_min_prio:
  assumes P: "valid_path P" and a: "a \<in> path_inf_priorities P"
  shows "Min (\<omega> ` V) \<le> a"
proof-
  have "a \<in> lset (ldropn 0 (lmap \<omega> P))" using a unfolding path_inf_priorities_def by blast
  hence "a \<in> \<omega> ` lset P" by simp
  thus ?thesis using P valid_path_in_V priorities_finite Min_le by blast
qed

lemma path_inf_priorities_LCons:
  "path_inf_priorities P = path_inf_priorities (LCons v P)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B" proof
    fix a assume "a \<in> ?A"
    hence "\<forall>n. a \<in> lset (ldropn n (lmap \<omega> (LCons v P)))"
      unfolding path_inf_priorities_def
      using in_lset_ltlD[of a] by (simp add: ltl_ldropn)
    thus "a \<in> ?B" unfolding path_inf_priorities_def by blast
  qed
next
  show "?B \<subseteq> ?A" proof
    fix a assume "a \<in> ?B"
    hence "\<forall>n. a \<in> lset (ldropn (Suc n) (lmap \<omega> (LCons v P)))"
      unfolding path_inf_priorities_def by blast
    thus "a \<in> ?A" unfolding path_inf_priorities_def by simp
  qed
qed
corollary path_inf_priorities_ltl: "path_inf_priorities P = path_inf_priorities (ltl P)"
  by (metis llist.exhaust ltl_simps path_inf_priorities_LCons)


subsection \<open>Winning Condition\<close>

text \<open>
  Let $G = (V,E,V_0,\omega)$ be a parity game.
  An infinite path $v_0,v_1,\ldots$ in $G$ is winning for player \Even (\Odd) if the minimum
  priority occurring infinitely often is even (odd).
  A finite path is winning for player @{term p} iff the last node on the path belongs to the other
  player.

  Empty paths are irrelevant, but it is useful to assign a fixed winner to them in order to get
  simpler lemmas.
\<close>

abbreviation "winning_priority p \<equiv> (if p = Even then even else odd)"

definition winning_path :: "Player \<Rightarrow> 'a Path \<Rightarrow> bool" where
  "winning_path p P \<equiv>
    (\<not>lfinite P \<and> (\<exists>a \<in> path_inf_priorities P.
      (\<forall>b \<in> path_inf_priorities P. a \<le> b) \<and> winning_priority p a))
    \<or> (\<not>lnull P \<and> lfinite P \<and> llast P \<in> VV p**)
    \<or> (lnull P \<and> p = Even)"

text \<open>Every path has a unique winner.\<close>
lemma paths_are_winning_for_one_player:
  assumes "valid_path P"
  shows "winning_path p P \<longleftrightarrow> \<not>winning_path p** P"
proof (cases)
  assume "\<not>lnull P"
  show ?thesis proof (cases)
    assume "lfinite P"
    thus ?thesis
      using assms lfinite_lset valid_path_in_V
      unfolding winning_path_def
      by auto
  next
    assume "\<not>lfinite P"
    then obtain a where "a \<in> path_inf_priorities P" "\<And>b. b < a \<Longrightarrow> b \<notin> path_inf_priorities P"
      using assms ex_least_nat_le[of "\<lambda>a. a \<in> path_inf_priorities P"] path_inf_priorities_is_nonempty
      by blast
    hence "\<forall>q. winning_priority q a \<longleftrightarrow> winning_path q P"
      unfolding winning_path_def using \<open>\<not>lnull P\<close> \<open>\<not>lfinite P\<close> by (metis le_antisym not_le)
    moreover have "\<forall>q. winning_priority p q \<longleftrightarrow> \<not>winning_priority p** q" by simp
    ultimately show ?thesis by blast
  qed
qed (simp add: winning_path_def)

lemma winning_path_ltl:
  assumes P: "winning_path p P" "\<not>lnull P" "\<not>lnull (ltl P)"
  shows "winning_path p (ltl P)"
proof (cases)
  assume "lfinite P"
  moreover have "llast P = llast (ltl P)"
    using P(2,3) by (metis llast_LCons2 ltl_simps(2) not_lnull_conv)
  ultimately show ?thesis using P by (simp add: winning_path_def)
next
  assume "\<not>lfinite P"
  thus ?thesis using winning_path_def path_inf_priorities_ltl P(1,2) by auto
qed

corollary winning_path_drop:
  assumes "winning_path p P" "enat n < llength P"
  shows "winning_path p (ldropn n P)"
using assms proof (induct n)
  case (Suc n)
  hence "winning_path p (ldropn n P)" using dual_order.strict_trans enat_ord_simps(2) by blast
  moreover have "ltl (ldropn n P) = ldropn (Suc n) P" by (simp add: ldrop_eSuc_ltl ltl_ldropn)
  moreover hence "\<not>lnull (ldropn n P)" using Suc.prems(2) by (metis leD lnull_ldropn lnull_ltlI)
  ultimately show ?case using winning_path_ltl[of p "ldropn n P"] Suc.prems(2) by auto
qed simp

corollary winning_path_drop_add:
  assumes "valid_path P" "winning_path p (ldropn n P)" "enat n < llength P"
  shows "winning_path p P"
  using assms paths_are_winning_for_one_player valid_path_drop winning_path_drop by blast

lemma winning_path_LCons:
  assumes P: "winning_path p P" "\<not>lnull P"
  shows "winning_path p (LCons v P)"
proof (cases)
  assume "lfinite P"
  moreover have "llast P = llast (LCons v P)"
    using P(2) by (metis llast_LCons2 not_lnull_conv)
  ultimately show ?thesis using P unfolding winning_path_def by simp
next
  assume "\<not>lfinite P"
  thus ?thesis using P path_inf_priorities_LCons unfolding winning_path_def by simp
qed

lemma winning_path_supergame:
  assumes "winning_path p P"
  and G': "ParityGame G'" "VV p** \<subseteq> ParityGame.VV G' p**" "\<omega> = \<omega>\<^bsub>G'\<^esub>"
  shows "ParityGame.winning_path G' p P"
proof-
  interpret G': ParityGame G' using G'(1) .
  have "\<lbrakk> lfinite P; \<not>lnull P \<rbrakk> \<Longrightarrow> llast P \<in> G'.VV p**" and "lnull P \<Longrightarrow> p = Even"
    using assms(1) unfolding winning_path_def using G'(2) by auto
  thus ?thesis unfolding G'.winning_path_def
    using lnull_imp_lfinite assms(1)
    unfolding winning_path_def path_inf_priorities_def G'.path_inf_priorities_def G'(3)
    by blast
qed

end \<comment> \<open>locale ParityGame\<close>

subsection \<open>Valid Maximal Paths\<close>

text \<open>Define a locale for valid maximal paths, because we need them often.\<close>

locale vm_path = ParityGame +
  fixes P v0
  assumes P_not_null [simp]: "\<not>lnull P"
      and P_valid    [simp]: "valid_path P"
      and P_maximal  [simp]: "maximal_path P"
      and P_v0       [simp]: "lhd P = v0"
begin
lemma P_LCons: "P = LCons v0 (ltl P)" using lhd_LCons_ltl[OF P_not_null] by simp

lemma P_len [simp]: "enat 0 < llength P" by (simp add: lnull_0_llength)
lemma P_0 [simp]: "P $ 0 = v0" by (simp add: lnth_0_conv_lhd)
lemma P_lnth_Suc: "P $ Suc n = ltl P $ n" by (simp add: lnth_ltl)
lemma P_no_deadends: "enat (Suc n) < llength P \<Longrightarrow> \<not>deadend (P $ n)"
  using valid_path_no_deadends by simp
lemma P_no_deadend_v0: "\<not>lnull (ltl P) \<Longrightarrow> \<not>deadend v0"
  by (metis P_LCons P_valid edges_are_in_V(2) not_lnull_conv valid_path_edges')
lemma P_no_deadend_v0_llength: "enat (Suc n) < llength P \<Longrightarrow> \<not>deadend v0"
  by (metis P_0 P_len P_valid enat_ord_simps(2) not_less_eq valid_path_ends_on_deadend zero_less_Suc)
lemma P_ends_on_deadend: "\<lbrakk> enat n < llength P; deadend (P $ n) \<rbrakk> \<Longrightarrow> enat (Suc n) = llength P"
  using P_valid valid_path_ends_on_deadend by blast

lemma P_lnull_ltl_deadend_v0: "lnull (ltl P) \<Longrightarrow> deadend v0"
  using P_LCons maximal_no_deadend by force
lemma P_lnull_ltl_LCons: "lnull (ltl P) \<Longrightarrow> P = LCons v0 LNil"
  using P_LCons lnull_def by metis
lemma P_deadend_v0_LCons: "deadend v0 \<Longrightarrow> P = LCons v0 LNil"
  using P_lnull_ltl_LCons P_no_deadend_v0 by blast

lemma Ptl_valid [simp]: "valid_path (ltl P)" using valid_path_ltl by auto
lemma Ptl_maximal [simp]: "maximal_path (ltl P)" using maximal_ltl by auto

lemma Pdrop_valid [simp]: "valid_path (ldropn n P)" using valid_path_drop by auto
lemma Pdrop_maximal [simp]: "maximal_path (ldropn n P)" using maximal_drop by auto

lemma prefix_valid [simp]: "valid_path (ltake n P)"
  using valid_path_prefix[of P] by auto

lemma extension_valid [simp]: "v\<rightarrow>v0 \<Longrightarrow> valid_path (LCons v P)"
  using P_not_null P_v0 P_valid valid_path_cons by blast
lemma extension_maximal [simp]: "maximal_path (LCons v P)"
  by (simp add: maximal_path_cons)
lemma lappend_maximal [simp]: "maximal_path (lappend P' P)"
  by (simp add: maximal_path_lappend)

lemma v0_V [simp]: "v0 \<in> V" by (metis P_LCons P_valid valid_path_cons_simp)
lemma v0_lset_P [simp]: "v0 \<in> lset P" using P_not_null P_v0 llist.set_sel(1) by blast
lemma v0_VV: "v0 \<in> VV p \<or> v0 \<in> VV p**" by simp
lemma lset_P_V [simp]: "lset P \<subseteq> V" by (simp add: valid_path_in_V)
lemma lset_ltl_P_V [simp]: "lset (ltl P) \<subseteq> V" by (simp add: valid_path_in_V)

lemma finite_llast_deadend [simp]: "lfinite P \<Longrightarrow> deadend (llast P)"
  using P_maximal P_not_null maximal_ends_on_deadend by blast
lemma finite_llast_V [simp]: "lfinite P \<Longrightarrow> llast P \<in> V"
  using P_not_null lfinite_lset lset_P_V by blast

text \<open>If a path visits a deadend, it is winning for the other player.\<close>
lemma visits_deadend:
  assumes "lset P \<inter> deadends p \<noteq> {}"
  shows "winning_path p** P"
proof-
  obtain n where n: "enat n < llength P" "P $ n \<in> deadends p"
    using assms by (meson lset_intersect_lnth)
  hence *: "enat (Suc n) = llength P" using P_ends_on_deadend unfolding deadends_def by blast
  hence "llast P = P $ n" by (simp add: eSuc_enat llast_conv_lnth)
  hence "llast P \<in> deadends p" using n(2) by simp
  moreover have "lfinite P" using * llength_eq_enat_lfiniteD by force
  ultimately show ?thesis unfolding winning_path_def deadends_def by auto
qed

end

end
