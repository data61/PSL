section \<open>Positional Determinacy of Parity Games\<close>

theory PositionalDeterminacy
imports
  Main
  AttractorStrategy
begin

context ParityGame begin

subsection \<open>Induction Step\<close>

text \<open>
  The proof of positional determinacy is by induction over the size of the finite set
  @{term "\<omega> ` V"}, the set of priorities.  The following lemma is the induction step.

  For now, we assume there are no deadends in the graph.  Later we will get rid of this assumption.
\<close>

lemma positional_strategy_induction_step:
  assumes "v \<in> V"
    and no_deadends: "\<And>v. v \<in> V \<Longrightarrow> \<not>deadend v"
    and IH: "\<And>(G :: ('a, 'b) ParityGame_scheme) v.
      \<lbrakk> card (\<omega>\<^bsub>G\<^esub> ` V\<^bsub>G\<^esub>) < card (\<omega> ` V); v \<in> V\<^bsub>G\<^esub>;
        ParityGame G;
        \<And>v. v \<in> V\<^bsub>G\<^esub> \<Longrightarrow> \<not>Digraph.deadend G v  \<rbrakk>
      \<Longrightarrow> \<exists>p. v \<in> ParityGame.winning_region G p"
  shows "\<exists>p. v \<in> winning_region p"
proof-
  text \<open>First, we determine the minimum priority and the player who likes it.\<close>
  define min_prio where "min_prio = Min (\<omega> ` V)"
  have "\<exists>p. winning_priority p min_prio" by auto
  then obtain p where p: "winning_priority p min_prio" by blast
  text \<open>Then we define the tentative winning region of player @{term "p**"}.
    The rest of the proof is to show that this is the complete winning region.
\<close>
  define W1 where "W1 = winning_region p**"
  text \<open>For this, we define several more sets of nodes.
    First, \<open>U\<close> is the tentative winning region of player @{term p}.
\<close>
  define U where "U = V - W1"
  define K where "K = U \<inter> (\<omega> -` {min_prio})"
  define V' where "V' = U - attractor p K"

  define G' where [simp]: "G' = subgame V'"
  interpret G': ParityGame G' using subgame_ParityGame by simp

  have U_equiv: "\<And>v. v \<in> V \<Longrightarrow> v \<in> U \<longleftrightarrow> v \<notin> winning_region p**"
    unfolding U_def W1_def by blast

  have "V' \<subseteq> V" unfolding U_def V'_def by blast
  hence [simp]: "V\<^bsub>G'\<^esub> = V'" unfolding G'_def by simp

  have "V\<^bsub>G'\<^esub> \<subseteq> V" "E\<^bsub>G'\<^esub> \<subseteq> E" "\<omega>\<^bsub>G'\<^esub> = \<omega>" unfolding G'_def by (simp_all add: subgame_\<omega>)
  have "G'.VV p = V' \<inter> VV p" unfolding G'_def using subgame_VV by simp

  have V_decomp: "V = attractor p K \<union> V' \<union> W1" proof-
    have "V \<subseteq> attractor p K \<union> V' \<union> W1"
      unfolding V'_def U_def by blast
    moreover have "attractor p K \<subseteq> V"
      using attractor_in_V[of K] unfolding K_def U_def by blast
    ultimately show ?thesis
      unfolding W1_def winning_region_def using \<open>V' \<subseteq> V\<close> by blast
  qed

  have G'_no_deadends: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> \<not>G'.deadend v" proof-
    fix v assume "v \<in> V\<^bsub>G'\<^esub>"
    hence *: "v \<in> U - attractor p K" using \<open>V\<^bsub>G'\<^esub> = V'\<close> V'_def by blast
    moreover hence "\<exists>w \<in> U. v\<rightarrow>w"
      using removing_winning_region_induces_no_deadends[of v "p**"] no_deadends U_equiv U_def
      by blast
    moreover have "\<And>w. \<lbrakk> v \<in> VV p**; v\<rightarrow>w \<rbrakk> \<Longrightarrow> w \<in> U"
      using * U_equiv winning_region_extends_VVp by blast
    ultimately have "\<exists>w \<in> V'. v\<rightarrow>w"
      using U_equiv winning_region_extends_VVp removing_attractor_induces_no_deadends V'_def
      by blast
    thus "\<not>G'.deadend v" using \<open>v \<in> V\<^bsub>G'\<^esub>\<close> \<open>V' \<subseteq> V\<close> by simp
  qed

  text \<open>
    By definition of @{term W1}, we obtain a winning strategy on @{term W1} for player @{term "p**"}.
\<close>
  obtain \<sigma>W1 where \<sigma>W1:
    "strategy p** \<sigma>W1" "\<And>v. v \<in> W1 \<Longrightarrow> winning_strategy p** \<sigma>W1 v"
    unfolding W1_def using merge_winning_strategies by blast

  {
    fix v assume "v \<in> V\<^bsub>G'\<^esub>"

    text \<open>Apply the induction hypothesis to get the winning strategy for @{term v} in @{term G'}.\<close>
    have G'_winning_strategy: "\<exists>p. v \<in> G'.winning_region p" proof-
      have "card (\<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>) < card (\<omega> ` V)" proof-
        { assume "min_prio \<in> \<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>"
          then obtain v where v: "v \<in> V\<^bsub>G'\<^esub>" "\<omega>\<^bsub>G'\<^esub> v = min_prio" by blast
          hence "v \<in> \<omega> -` {min_prio}" using \<open>\<omega>\<^bsub>G'\<^esub> = \<omega>\<close> by simp
          hence False using V'_def K_def attractor_set_base \<open>V\<^bsub>G'\<^esub> = V'\<close> v(1)
            by (metis DiffD1 DiffD2 IntI contra_subsetD)
        }
        hence "min_prio \<notin> \<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub>" by blast
        moreover have "min_prio \<in> \<omega> ` V"
          unfolding min_prio_def using priorities_finite Min_in assms(1) by blast
        moreover have "\<omega>\<^bsub>G'\<^esub> ` V\<^bsub>G'\<^esub> \<subseteq> \<omega> ` V" unfolding G'_def by simp
        ultimately show ?thesis by (metis priorities_finite psubsetI psubset_card_mono)
      qed
      thus ?thesis using IH[of G'] \<open>v \<in> V\<^bsub>G'\<^esub>\<close> G'_no_deadends G'.ParityGame_axioms by blast
    qed

    text \<open>
      It turns out the winning region of player @{term "p**"} is empty, so we have a strategy
      for player @{term p}.
\<close>
    have "v \<in> G'.winning_region p" proof (rule ccontr)
      assume "\<not>?thesis"
      moreover obtain p' \<sigma> where p': "G'.strategy p' \<sigma>" "G'.winning_strategy p' \<sigma> v"
        using G'_winning_strategy unfolding G'.winning_region_def by blast
      ultimately have "p' \<noteq> p" using \<open>v \<in> V\<^bsub>G'\<^esub>\<close> unfolding G'.winning_region_def by blast
      hence "p' = p**" by (cases p; cases p') auto
      with p' have \<sigma>: "G'.strategy p** \<sigma>" "G'.winning_strategy p** \<sigma> v" by simp_all

      have "v \<in> winning_region p**" proof
        show "v \<in> V" using \<open>v \<in> V\<^bsub>G'\<^esub>\<close> \<open>V\<^bsub>G'\<^esub> \<subseteq> V\<close> by blast
        define \<sigma>' where "\<sigma>' = override_on (override_on \<sigma>_arbitrary \<sigma>W1 W1) \<sigma> V'"
        thus "strategy p** \<sigma>'"
          using valid_strategy_updates_set_strong valid_arbitrary_strategy \<sigma>W1(1)
                valid_strategy_supergame \<sigma>(1) G'_no_deadends \<open>V\<^bsub>G'\<^esub> = V'\<close>
          unfolding G'_def by blast
        show "winning_strategy p** \<sigma>' v"
        proof (rule winning_strategyI, rule ccontr)
          fix P assume "vmc_path G P v p** \<sigma>'"
          then interpret vmc_path G P v "p**" \<sigma>' .
          assume "\<not>winning_path p** P"
          text \<open>
            First we show that @{term P} stays in @{term V'}, because if it stays in @{term V'},
            then it conforms to @{term \<sigma>}, so it must be winning for @{term "p**"}.\<close>

          have "lset P \<subseteq> V'" proof (induct rule: vmc_path_lset_induction_closed_subset)
            fix v assume "v \<in> V'" "\<not>deadend v" "v \<in> VV p**"
            hence "v \<in> ParityGame.VV (subgame V') p**" by auto
            moreover have "\<not>G'.deadend v" using G'_no_deadends \<open>V\<^bsub>G'\<^esub> = V'\<close> \<open>v \<in> V'\<close> by blast
            ultimately have "\<sigma> v \<in> V'"
              using subgame_strategy_stays_in_subgame p'(1) \<open>p' = p**\<close>
              unfolding G'_def by blast
            thus "\<sigma>' v \<in> V' \<union> W1" unfolding \<sigma>'_def using \<open>v \<in> V'\<close> by simp
          next
            fix v w assume "v \<in> V'" "\<not>deadend v" "v \<in> VV p****" "v\<rightarrow>w"
            show "w \<in> V' \<union> W1" proof (rule ccontr)
              assume "w \<notin> V' \<union> W1"
              hence "w \<in> attractor p K" using V_decomp \<open>v\<rightarrow>w\<close> by blast
              hence "v \<in> attractor p K" using \<open>v \<in> VV p****\<close> attractor_set_VVp \<open>v\<rightarrow>w\<close> by auto
              thus False using \<open>v \<in> V'\<close> V'_def by blast
            qed
          next
            have "\<And>v. v \<in> W1 \<Longrightarrow> \<sigma>W1 v = \<sigma>' v" unfolding \<sigma>'_def V'_def U_def by simp
            thus "lset P \<inter> W1 = {}"
              using path_hits_winning_region_is_winning \<sigma>W1 \<open>\<not>winning_path p** P\<close>
              unfolding W1_def
              by blast
          next
            show "v \<in> V'" using \<open>V\<^bsub>G'\<^esub> = V'\<close> \<open>v \<in> V\<^bsub>G'\<^esub>\<close> by blast
          qed
          text \<open>This concludes the proof of @{term "lset P \<subseteq> V'"}.\<close>
          hence "G'.valid_path P" using subgame_valid_path by simp
          moreover have "G'.maximal_path P"
            using \<open>lset P \<subseteq> V'\<close> subgame_maximal_path \<open>V' \<subseteq> V\<close> by simp
          moreover have "G'.path_conforms_with_strategy p** P \<sigma>" proof-
            have "G'.path_conforms_with_strategy p** P \<sigma>'"
              using subgame_path_conforms_with_strategy \<open>V' \<subseteq> V\<close> \<open>lset P \<subseteq> V'\<close>
              by simp
            moreover have "\<And>v. v \<in> lset P \<Longrightarrow> \<sigma>' v = \<sigma> v" using \<open>lset P \<subseteq> V'\<close> \<sigma>'_def by auto
            ultimately show ?thesis
              using G'.path_conforms_with_strategy_irrelevant_updates by blast
          qed
          ultimately have "G'.winning_path p** P"
            using \<sigma>(2) G'.winning_strategy_def G'.valid_maximal_conforming_path_0 P_0 P_not_null
            by blast
          moreover have "G'.VV p**** \<subseteq> VV p****" using subgame_VV_subset G'_def by blast
          ultimately show False
            using G'.winning_path_supergame[of "p**"] \<open>\<omega>\<^bsub>G'\<^esub> = \<omega>\<close>
                  \<open>\<not>winning_path p** P\<close> ParityGame_axioms
            by blast
        qed
      qed
      moreover have "v \<in> V" using \<open>V\<^bsub>G'\<^esub> \<subseteq> V\<close> \<open>v \<in> V\<^bsub>G'\<^esub>\<close> by blast
      ultimately have "v \<in> W1" unfolding W1_def winning_region_def by blast
      thus False using \<open>v \<in> V\<^bsub>G'\<^esub>\<close> using U_def V'_def \<open>V\<^bsub>G'\<^esub> = V'\<close> \<open>v \<in> V\<^bsub>G'\<^esub>\<close> by blast
    qed
  } note recursion = this

  text \<open>
    We compose a winning strategy for player @{term p} on @{term "V - W1"} out of three pieces.
\<close>

  text \<open>
    First, if we happen to land in the attractor region of @{term K}, we follow the attractor
    strategy.  This is good because the priority of the nodes in @{term K} is good for
    player @{term p}, so he likes to go there.\<close>
  obtain \<sigma>1
    where \<sigma>1: "strategy p \<sigma>1"
              "strategy_attracts p \<sigma>1 (attractor p K) K"
    using attractor_has_strategy[of K p] K_def U_def by auto

  text \<open>Next, on @{term G'} we follow the winning strategy whose existence we proved earlier.\<close>
  have "G'.winning_region p = V\<^bsub>G'\<^esub>" using recursion unfolding G'.winning_region_def by blast
  then obtain \<sigma>2
    where \<sigma>2: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> G'.strategy p \<sigma>2"
              "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> G'.winning_strategy p \<sigma>2 v"
    using G'.merge_winning_strategies by blast

  text \<open>
    As a last option we choose an arbitrary successor but avoid entering @{term W1}.
    In particular, this defines the strategy on the set @{term K}.\<close>
  define succ where "succ v = (SOME w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1))" for v

  text \<open>Compose the three pieces.\<close>
  define \<sigma> where "\<sigma> = override_on (override_on succ \<sigma>2 V') \<sigma>1 (attractor p K - K)"

  have "attractor p K \<inter> W1 = {}" proof (rule ccontr)
    assume "attractor p K \<inter> W1 \<noteq> {}"
    then obtain v where v: "v \<in> attractor p K" "v \<in> W1" by blast
    hence "v \<in> V" using W1_def winning_region_def by blast
    obtain P where "vmc2_path G P v p \<sigma>1 \<sigma>W1"
      using strategy_conforming_path_exists \<sigma>W1(1) \<sigma>1(1) \<open>v \<in> V\<close> by blast
    then interpret vmc2_path G P v p \<sigma>1 \<sigma>W1 .
    have "strategy_attracts_via p \<sigma>1 v (attractor p K) K" using v(1) \<sigma>1(2) strategy_attracts_def by blast
    hence "lset P \<inter> K \<noteq> {}" using strategy_attracts_viaE visits_via_visits by blast
    hence "\<not>lset P \<subseteq> W1" unfolding K_def U_def by blast
    thus False unfolding W1_def using comp.paths_stay_in_winning_region \<sigma>W1 v(2) by auto
  qed

  text \<open>On specific sets, @{term \<sigma>} behaves like one of the three pieces.\<close>
  have \<sigma>_\<sigma>1: "\<And>v. v \<in> attractor p K - K \<Longrightarrow> \<sigma> v = \<sigma>1 v" unfolding \<sigma>_def by simp
  have \<sigma>_\<sigma>2: "\<And>v. v \<in> V' \<Longrightarrow> \<sigma> v = \<sigma>2 v" unfolding \<sigma>_def V'_def by auto
  have \<sigma>_K: "\<And>v. v \<in> K \<union> W1 \<Longrightarrow> \<sigma> v = succ v" proof-
    fix v assume v: "v \<in> K \<union> W1"
    hence "v \<notin> V'" unfolding V'_def U_def using attractor_set_base by auto
    with v show "\<sigma> v = succ v" unfolding \<sigma>_def U_def using \<open>attractor p K \<inter> W1 = {}\<close>
      by (metis (mono_tags, lifting) Diff_iff IntI UnE override_on_def override_on_emptyset)
  qed

  text \<open>Show that @{term succ} succeeds in avoiding entering @{term W1}.\<close>
  { fix v assume v: "v \<in> VV p"
    hence "\<not>deadend v" using no_deadends by blast
    have "\<exists>w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1)" proof (cases)
      assume "v \<in> W1"
      thus ?thesis using no_deadends \<open>\<not>deadend v\<close> by blast
    next
      assume "v \<notin> W1"
      show ?thesis proof (rule ccontr)
        assume "\<not>(\<exists>w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1))"
        hence "\<And>w. v\<rightarrow>w \<Longrightarrow> winning_strategy p** \<sigma>W1 w" using \<sigma>W1(2) by blast
        hence "winning_strategy p** \<sigma>W1 v"
          using strategy_extends_backwards_VVpstar \<sigma>W1(1) \<open>v \<in> VV p\<close> by simp
        hence "v \<in> W1" unfolding W1_def winning_region_def using \<sigma>W1(1) \<open>\<not>deadend v\<close> by blast
        thus False using \<open>v \<notin> W1\<close> by blast
      qed
    qed
    hence "v\<rightarrow>succ v" "v \<in> W1 \<or> succ v \<notin> W1" unfolding succ_def
      using someI_ex[of "\<lambda>w. v\<rightarrow>w \<and> (v \<in> W1 \<or> w \<notin> W1)"] by blast+
  } note succ_works = this

  have "strategy p \<sigma>"
  proof
    fix v assume v: "v \<in> VV p" "\<not>deadend v"
    hence "v \<in> attractor p K - K \<Longrightarrow> v\<rightarrow>\<sigma> v" using \<sigma>_\<sigma>1 \<sigma>1(1) v unfolding strategy_def by auto
    moreover have "v \<in> V' \<Longrightarrow> v\<rightarrow>\<sigma> v" proof-
      assume "v \<in> V'"
      moreover have "v \<in> V\<^bsub>G'\<^esub>" using \<open>v \<in> V'\<close> \<open>V\<^bsub>G'\<^esub> = V'\<close> by blast
      moreover have "v \<in> G'.VV p" using \<open>G'.VV p = V' \<inter> VV p\<close> \<open>v \<in> V'\<close> \<open>v \<in> VV p\<close> by blast
      moreover have "\<not>Digraph.deadend G' v" using G'_no_deadends \<open>v \<in> V\<^bsub>G'\<^esub>\<close> by blast
      ultimately have "v \<rightarrow>\<^bsub>G'\<^esub> \<sigma>2 v" using \<sigma>2(1) G'.strategy_def[of p \<sigma>2] by blast
      with \<open>v \<in> V'\<close> show "v\<rightarrow>\<sigma> v" using \<open>E\<^bsub>G'\<^esub> \<subseteq> E\<close> \<sigma>_\<sigma>2 by (metis subsetCE)
    qed
    moreover have "v \<in> K \<union> W1 \<Longrightarrow> v\<rightarrow>\<sigma> v" using succ_works(1) v \<sigma>_K by auto
    moreover have "v \<in> V" using \<open>v \<in> VV p\<close> by blast
    ultimately show "v\<rightarrow>\<sigma> v" using V_decomp by blast
  qed

  have \<sigma>_attracts: "strategy_attracts p \<sigma> (attractor p K) K" proof-
    have "strategy_attracts p (override_on \<sigma> \<sigma>1 (attractor p K - K)) (attractor p K) K"
      using strategy_attracts_irrelevant_override \<sigma>1 \<open>strategy p \<sigma>\<close> by blast
    moreover have "\<sigma> = override_on \<sigma> \<sigma>1 (attractor p K - K)"
      by (rule ext) (simp add: override_on_def \<sigma>_\<sigma>1)
    ultimately show ?thesis by simp
  qed

  text \<open>Show that @{term \<sigma>} is a winning strategy on @{term "V - W1"}.\<close>
  have "\<forall>v \<in> V - W1. winning_strategy p \<sigma> v" proof (intro ballI winning_strategyI)
    fix v P assume P: "v \<in> V - W1" "vmc_path G P v p \<sigma>"
    interpret vmc_path G P v p \<sigma> using P(2) .

    have "lset P \<subseteq> V - W1"
    proof (induct rule: vmc_path_lset_induction_closed_subset)
      fix v assume "v \<in> V - W1" "\<not>deadend v" "v \<in> VV p"
      show "\<sigma> v \<in> V - W1 \<union> {}" proof (rule ccontr)
        assume "\<not>?thesis"
        hence "\<sigma> v \<in> W1"
          using \<open>strategy p \<sigma>\<close> \<open>\<not>deadend v\<close> \<open>v \<in> VV p\<close>
          unfolding strategy_def by blast
        hence "v \<notin> K" using succ_works(2)[OF \<open>v \<in> VV p\<close>] \<open>v \<in> V - W1\<close> \<sigma>_K by auto
        moreover have "v \<notin> attractor p K - K" proof
          assume "v \<in> attractor p K - K"
          hence "\<sigma> v \<in> attractor p K"
            using attracted_strategy_step \<open>strategy p \<sigma>\<close> \<sigma>_attracts \<open>\<not>deadend v\<close> \<open>v \<in> VV p\<close>
                  attractor_set_base
            by blast
          thus False using \<open>\<sigma> v \<in> W1\<close> \<open>attractor p K \<inter> W1 = {}\<close> by blast
        qed
        moreover have "v \<notin> V'" proof
          assume "v \<in> V'"
          have "\<sigma>2 v \<in> V\<^bsub>G'\<^esub>" proof (rule G'.valid_strategy_in_V[of p \<sigma>2 v])
            have "v \<in> V\<^bsub>G'\<^esub>" using \<open>V\<^bsub>G'\<^esub> = V'\<close> \<open>v \<in> V'\<close> by simp
            thus "\<not>G'.deadend v" using G'_no_deadends by blast
            show "G'.strategy p \<sigma>2" using \<sigma>2(1) \<open>v \<in> V\<^bsub>G'\<^esub>\<close> by blast
            show "v \<in> G'.VV p" using \<open>v \<in> VV p\<close> \<open>G'.VV p = V' \<inter> VV p\<close> \<open>v \<in> V'\<close> by simp
          qed
          hence "\<sigma> v \<in> V\<^bsub>G'\<^esub>" using \<open>v \<in> V'\<close> \<sigma>_\<sigma>2 by simp
          thus False using \<open>V\<^bsub>G'\<^esub> = V'\<close> \<open>\<sigma> v \<in> W1\<close> V'_def U_def by blast
        qed
        ultimately show False using \<open>v \<in> V - W1\<close> V_decomp by blast
      qed
    next
      fix v w assume "v \<in> V - W1" "\<not>deadend v" "v \<in> VV p**" "v\<rightarrow>w"
      show "w \<in> V - W1 \<union> {}"
      proof (rule ccontr)
        assume "\<not>?thesis"
        hence "w \<in> W1" using \<open>v\<rightarrow>w\<close> by blast
        let ?\<sigma> = "\<sigma>W1(v := w)"
        have "winning_strategy p** \<sigma>W1 w" using \<open>w \<in> W1\<close> \<sigma>W1(2) by blast
        moreover have "\<not>(\<exists>\<sigma>. strategy p** \<sigma> \<and> winning_strategy p** \<sigma> v)"
          using \<open>v \<in> V - W1\<close> unfolding W1_def winning_region_def by blast
        ultimately have "winning_strategy p** ?\<sigma> w"
          using winning_strategy_updates[of "p**" \<sigma>W1 w v w] \<sigma>W1(1) \<open>v\<rightarrow>w\<close>
          unfolding winning_region_def by blast
        moreover have "strategy p** ?\<sigma>" using \<open>v\<rightarrow>w\<close> \<sigma>W1(1) valid_strategy_updates by blast
        ultimately have "winning_strategy p** ?\<sigma> v"
          using strategy_extends_backwards_VVp[of v "p**" ?\<sigma> w]
                \<open>v \<in> VV p**\<close> \<open>v\<rightarrow>w\<close>
          by auto
        hence "v \<in> W1" unfolding W1_def winning_region_def
          using \<open>strategy p** ?\<sigma>\<close> \<open>v \<in> V - W1\<close> by blast
        thus False using \<open>v \<in> V - W1\<close> by blast
      qed
    qed (insert P(1), simp_all)
    text \<open>This concludes the proof of @{term "lset P \<subseteq> V - W1"}.\<close>
    hence "lset P \<subseteq> attractor p K \<union> V'" using V_decomp by blast

    have "\<not>lfinite P"
      using no_deadends lfinite_lset maximal_ends_on_deadend[of P] P_maximal P_not_null lset_P_V
      by blast

    text \<open>
      Every @{term \<sigma>}-conforming path starting in @{term "V - W1"} is winning.
      We distinguish two cases:
      \begin{enumerate}
        \item @{term P} eventually stays in @{term V'}.
          Then @{term P} is winning because @{term \<sigma>2} is winning.
        \item @{term P} visits @{term K} infinitely often.
          Then @{term P} is winning because of the priority of the nodes in @{term K}.
      \end{enumerate}
\<close>
    show "winning_path p P"
    proof (cases)
      assume "\<exists>n. lset (ldropn n P) \<subseteq> V'"
      text \<open>The first case: @{term P} eventually stays in @{term V'}.\<close>
      then obtain n where n: "lset (ldropn n P) \<subseteq> V'" by blast
      define P' where "P' = ldropn n P"
      hence "lset P' \<subseteq> V'" using n by blast
      interpret vmc_path': vmc_path G' P' "lhd P'" p \<sigma>2 proof
        show "\<not>lnull P'" unfolding P'_def
          using \<open>\<not>lfinite P\<close> lfinite_ldropn lnull_imp_lfinite by blast
        show "G'.valid_path P'" proof-
          have "valid_path P'" unfolding P'_def by simp
          thus ?thesis using subgame_valid_path \<open>lset P' \<subseteq> V'\<close> G'_def by blast
        qed
        show "G'.maximal_path P'" proof-
          have "maximal_path P'" unfolding P'_def by simp
          thus ?thesis using subgame_maximal_path \<open>lset P' \<subseteq> V'\<close> \<open>V' \<subseteq> V\<close> G'_def by blast
        qed
        show "G'.path_conforms_with_strategy p P' \<sigma>2" proof-
          have "path_conforms_with_strategy p P' \<sigma>" unfolding P'_def by simp
          hence "path_conforms_with_strategy p P' \<sigma>2"
            using path_conforms_with_strategy_irrelevant_updates \<open>lset P' \<subseteq> V'\<close> \<sigma>_\<sigma>2
            by blast
          thus ?thesis
            using subgame_path_conforms_with_strategy \<open>lset P' \<subseteq> V'\<close> \<open>V' \<subseteq> V\<close> G'_def
            by blast
        qed
      qed simp
      have "G'.winning_strategy p \<sigma>2 (lhd P')"
        using \<open>lset P' \<subseteq> V'\<close> vmc_path'.P_not_null \<sigma>2(2)[of "lhd P'"] \<open>V\<^bsub>G'\<^esub> = V'\<close> llist.set_sel(1)
        by blast
      hence "G'.winning_path p P'" using G'.winning_strategy_def vmc_path'.vmc_path_axioms by blast
      moreover have "G'.VV p** \<subseteq> VV p**" unfolding G'_def using subgame_VV by simp
      ultimately have "winning_path p P'"
        using G'.winning_path_supergame[of p P' G] \<open>\<omega>\<^bsub>G'\<^esub> = \<omega>\<close> ParityGame_axioms by blast
      thus ?thesis
        unfolding P'_def
        using infinite_small_llength[OF \<open>\<not>lfinite P\<close>]
              winning_path_drop_add[of P p n] P_valid
        by blast
    next
      assume asm: "\<not>(\<exists>n. lset (ldropn n P) \<subseteq> V')"
      text \<open>The second case: @{term P} visits @{term K} infinitely often.
        Then @{term min_prio} occurs infinitely often on @{term P}.\<close>
      have "min_prio \<in> path_inf_priorities P"
      unfolding path_inf_priorities_def proof (intro CollectI allI)
        fix n
        obtain k1 where k1: "ldropn n P $ k1 \<notin> V'" using asm by (metis lset_lnth subsetI)
        define k2 where "k2 = k1 + n"
        interpret vmc_path G "ldropn k2 P" "P $ k2" p \<sigma>
          using vmc_path_ldropn infinite_small_llength \<open>\<not>lfinite P\<close> by blast
        have "P $ k2 \<notin> V'" unfolding k2_def
          using k1 lnth_ldropn infinite_small_llength[OF \<open>\<not>lfinite P\<close>] by simp
        hence "P $ k2 \<in> attractor p K" using \<open>\<not>lfinite P\<close> \<open>lset P \<subseteq> V - W1\<close>
          by (metis DiffI U_def V'_def lset_nth_member_inf)
        then obtain k3 where k3: "ldropn k2 P $ k3 \<in> K"
          using \<sigma>_attracts strategy_attractsE unfolding G'.visits_via_def by blast
        define k4 where "k4 = k3 + k2"
        hence "P $ k4 \<in> K"
          using k3 lnth_ldropn infinite_small_llength[OF \<open>\<not>lfinite P\<close>] by simp
        moreover have "k4 \<ge> n" unfolding k4_def k2_def
          using le_add2 le_trans by blast
        moreover have "ldropn n P $ k4 - n = P $ (k4 - n) + n"
          using lnth_ldropn infinite_small_llength \<open>\<not>lfinite P\<close> by blast
        ultimately have "ldropn n P $ k4 - n \<in> K" by simp
        hence "lset (ldropn n P) \<inter> K \<noteq> {}"
          using \<open>\<not>lfinite P\<close> lfinite_ldropn in_lset_conv_lnth[of "ldropn n P $ k4 - n"]
          by blast
        thus "min_prio \<in> lset (ldropn n (lmap \<omega> P))" unfolding K_def by auto
      qed
      thus ?thesis unfolding winning_path_def
        using path_inf_priorities_at_least_min_prio[OF P_valid, folded min_prio_def]
              \<open>winning_priority p min_prio\<close> \<open>\<not>lfinite P\<close>
        by blast
    qed
  qed
  hence "\<forall>v \<in> V. \<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v"
    unfolding W1_def winning_region_def using \<open>strategy p \<sigma>\<close> by blast
  hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v" using \<open>v \<in> V\<close> by simp
  thus ?thesis unfolding winning_region_def using \<open>v \<in> V\<close> by blast
qed


subsection \<open>Positional Determinacy without Deadends\<close>

theorem positional_strategy_exists_without_deadends:
  assumes "v \<in> V" "\<And>v. v \<in> V \<Longrightarrow> \<not>deadend v"
  shows "\<exists>p. v \<in> winning_region p"
  using assms ParityGame_axioms
  by (induct "card (\<omega> ` V)" arbitrary: G v rule: nat_less_induct)
     (rule ParityGame.positional_strategy_induction_step, simp_all)


subsection \<open>Positional Determinacy with Deadends\<close>

text \<open>
  Prove a stronger version of the previous theorem: Allow deadends.
\<close>
theorem positional_strategy_exists:
  assumes "v0 \<in> V"
  shows "\<exists>p. v0 \<in> winning_region p"
proof-
  { fix p
    define A where "A = attractor p (deadends p**)"
    assume v0_in_attractor: "v0 \<in> attractor p (deadends p**)"
    then obtain \<sigma> where \<sigma>: "strategy p \<sigma>" "strategy_attracts p \<sigma> A (deadends p**)"
      using attractor_has_strategy[of "deadends p**" "p"] A_def deadends_in_V by blast

    have "A \<subseteq> V" using A_def using attractor_in_V deadends_in_V by blast
    hence "A - deadends p** \<subseteq> V" by auto

    have "winning_strategy p \<sigma> v0" proof (unfold winning_strategy_def, intro allI impI)
      fix P assume "vmc_path G P v0 p \<sigma>"
      then interpret vmc_path G P v0 p \<sigma> .
      show "winning_path p P"
        using visits_deadend[of "p**"] \<sigma>(2) strategy_attracts_lset v0_in_attractor
        unfolding A_def by simp
    qed
    hence "\<exists>p \<sigma>. strategy p \<sigma> \<and> winning_strategy p \<sigma> v0" using \<sigma> by blast
  } note lemma_path_to_deadend = this
  define A where "A p = attractor p (deadends p**)" for p
  text \<open>Remove the attractor sets of the sets of deadends.\<close>
  define V' where "V' = V - A Even - A Odd"
  hence "V' \<subseteq> V" by blast
  show ?thesis proof (cases)
    assume "v0 \<in> V'"
    define G' where "G' = subgame V'"
    interpret G': ParityGame G' unfolding G'_def using subgame_ParityGame .
    have "V\<^bsub>G'\<^esub> = V'" unfolding G'_def using \<open>V' \<subseteq> V\<close> by simp
    hence "v0 \<in> V\<^bsub>G'\<^esub>" using \<open>v0 \<in> V'\<close> by simp
    moreover have V'_no_deadends: "\<And>v. v \<in> V\<^bsub>G'\<^esub> \<Longrightarrow> \<not>G'.deadend v" proof-
      fix v assume "v \<in> V\<^bsub>G'\<^esub>"
      moreover have "V' = V - A Even - A Even**" using V'_def by simp
      ultimately show "\<not>G'.deadend v"
        using subgame_without_deadends \<open>v \<in> V\<^bsub>G'\<^esub>\<close> unfolding A_def G'_def by blast
    qed
    ultimately obtain p \<sigma> where \<sigma>: "G'.strategy p \<sigma>" "G'.winning_strategy p \<sigma> v0"
      using G'.positional_strategy_exists_without_deadends
      unfolding G'.winning_region_def
      by blast

    have V'_no_deadends': "\<And>v. v \<in> V' \<Longrightarrow> \<not>deadend v" proof-
      fix v assume "v \<in> V'"
      hence "\<not>G'.deadend v" using V'_no_deadends \<open>V' \<subseteq> V\<close> unfolding G'_def by auto
      thus "\<not>deadend v" unfolding G'_def using \<open>V' \<subseteq> V\<close> by auto
    qed

    obtain \<sigma>_attr
      where \<sigma>_attr: "strategy p \<sigma>_attr" "strategy_attracts p \<sigma>_attr (A p) (deadends p**)"
      using attractor_has_strategy[OF deadends_in_V] unfolding A_def by blast
    define \<sigma>' where "\<sigma>' = override_on \<sigma> \<sigma>_attr (A Even \<union> A Odd)"
    have \<sigma>'_is_\<sigma>_on_V': "\<And>v. v \<in> V' \<Longrightarrow> \<sigma>' v = \<sigma> v"
      unfolding V'_def \<sigma>'_def A_def by (cases p) simp_all

    have "strategy p \<sigma>'" proof-
      have "\<sigma>' = override_on \<sigma>_attr \<sigma> (UNIV - A Even - A Odd)"
        unfolding \<sigma>'_def override_on_def by (rule ext) simp
      moreover have "strategy p (override_on \<sigma>_attr \<sigma> V')"
        using valid_strategy_supergame \<sigma>_attr(1) \<sigma>(1) V'_no_deadends \<open>V\<^bsub>G'\<^esub> = V'\<close>
        unfolding G'_def by blast
      ultimately show ?thesis by (simp add: valid_strategy_only_in_V V'_def override_on_def)
    qed
    moreover have "winning_strategy p \<sigma>' v0" proof (rule winning_strategyI, rule ccontr)
      fix P assume "vmc_path G P v0 p \<sigma>'"
      then interpret vmc_path G P v0 p \<sigma>' .
      interpret vmc_path_no_deadend G P v0 p \<sigma>'
        using V'_no_deadends' \<open>v0 \<in> V'\<close> by unfold_locales
      assume contra: "\<not>winning_path p P"

      have "lset P \<subseteq> V'" proof (induct rule: vmc_path_lset_induction_closed_subset)
        fix v assume "v \<in> V'" "\<not>deadend v" "v \<in> VV p"
        hence "v \<in> G'.VV p" unfolding G'_def by (simp add: \<open>v \<in> V'\<close>)
        moreover have "\<not>G'.deadend v" using V'_no_deadends \<open>v \<in> V'\<close> \<open>V\<^bsub>G'\<^esub> = V'\<close> by blast
        moreover have "G'.strategy p \<sigma>'"
          using G'.valid_strategy_only_in_V \<sigma>'_def \<sigma>'_is_\<sigma>_on_V' \<sigma>(1) \<open>V\<^bsub>G'\<^esub> = V'\<close> by auto
        ultimately show "\<sigma>' v \<in> V' \<union> A p" using subgame_strategy_stays_in_subgame
          unfolding G'_def by blast
      next
        fix v w assume "v \<in> V'" "\<not>deadend v" "v \<in> VV p**" "v\<rightarrow>w"
        have "w \<notin> A p**" proof
          assume "w \<in> A p**"
          hence "v \<in> A p**" unfolding A_def
            using \<open>v \<in> VV p**\<close> \<open>v\<rightarrow>w\<close> attractor_set_VVp by blast
          thus False using \<open>v \<in> V'\<close> unfolding V'_def by (cases p) auto
        qed
        thus "w \<in> V' \<union> A p" unfolding V'_def using \<open>v\<rightarrow>w\<close> by (cases p) auto
      next
        show "lset P \<inter> A p = {}" proof (rule ccontr)
          assume "lset P \<inter> A p \<noteq> {}"
          have "strategy_attracts p (override_on \<sigma>' \<sigma>_attr (A p - deadends p**))
                                    (A p)
                                    (deadends p**)"
            using strategy_attracts_irrelevant_override[OF \<sigma>_attr(2) \<sigma>_attr(1) \<open>strategy p \<sigma>'\<close>]
            by blast
          moreover have "override_on \<sigma>' \<sigma>_attr (A p - deadends p**) = \<sigma>'"
            by (rule ext, unfold \<sigma>'_def, cases p) (simp_all add: override_on_def)
          ultimately have "strategy_attracts p \<sigma>' (A p) (deadends p**)" by simp
          hence "lset P \<inter> deadends p** \<noteq> {}"
            using \<open>lset P \<inter> A p \<noteq> {}\<close> attracted_path[OF deadends_in_V] by simp
          thus False using contra visits_deadend[of "p**"] by simp
        qed
      qed (insert \<open>v0 \<in> V'\<close>)

      then interpret vmc_path G' P v0 p \<sigma>'
        unfolding G'_def using subgame_path_vmc_path[OF \<open>V' \<subseteq> V\<close>] by blast
      have "G'.path_conforms_with_strategy p P \<sigma>" proof-
        have "\<And>v. v \<in> lset P \<Longrightarrow> \<sigma>' v = \<sigma> v"
          using \<sigma>'_is_\<sigma>_on_V' \<open>V\<^bsub>G'\<^esub> = V'\<close> lset_P_V by blast
        thus "G'.path_conforms_with_strategy p P \<sigma>"
          using P_conforms G'.path_conforms_with_strategy_irrelevant_updates by blast
      qed
      then interpret vmc_path G' P v0 p \<sigma> using conforms_to_another_strategy by blast
      have "G'.winning_path p P"
        using \<sigma>(2)[unfolded G'.winning_strategy_def] vmc_path_axioms by blast
      from \<open>\<not>winning_path p P\<close>
           G'.winning_path_supergame[OF this ParityGame_axioms, unfolded G'_def]
           subgame_VV_subset[of "p**" V']
           subgame_\<omega>[of V']
        show False by blast
    qed
    ultimately show ?thesis unfolding winning_region_def using \<open>v0 \<in> V\<close> by blast
  next
    assume "v0 \<notin> V'"
    then obtain p where "v0 \<in> attractor p (deadends p**)"
      unfolding V'_def A_def using \<open>v0 \<in> V\<close> by blast
    thus ?thesis unfolding winning_region_def
      using lemma_path_to_deadend \<open>v0 \<in> V\<close> by blast
  qed
qed

subsection \<open>The Main Theorem: Positional Determinacy\<close>
text \<open>\label{subsec:positional_determinacy}\<close>

text \<open>
  Prove the main theorem: The winning regions of player \Even and \Odd are a partition of the set
  of nodes @{term V}.
\<close>

theorem partition_into_winning_regions:
  shows "V = winning_region Even \<union> winning_region Odd"
    and "winning_region Even \<inter> winning_region Odd = {}"
proof
  show "V \<subseteq> winning_region Even \<union> winning_region Odd"
    by (rule subsetI) (metis (full_types) Un_iff other_other_player positional_strategy_exists)
next
  show "winning_region Even \<union> winning_region Odd \<subseteq> V"
    by (rule subsetI) (meson Un_iff subsetCE winning_region_in_V)
next
  show "winning_region Even \<inter> winning_region Odd = {}"
    using winning_strategy_only_for_one_player[of Even]
    unfolding winning_region_def by auto
qed

end \<comment> \<open>context ParityGame\<close>

end
