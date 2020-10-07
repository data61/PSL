section \<open>Rankings\<close>

theory Ranking
imports
  "Alternate"
  "Graph"
begin

  subsection \<open>Rankings\<close>

  type_synonym 'state ranking = "'state node \<Rightarrow> nat"

  definition ranking :: "('label, 'state) nba \<Rightarrow> 'label stream \<Rightarrow> 'state ranking \<Rightarrow> bool" where
    "ranking A w f \<equiv>
      (\<forall> v \<in> gunodes A w. f v \<le> 2 * card (nodes A)) \<and>
      (\<forall> v \<in> gunodes A w. \<forall> u \<in> gusuccessors A w v. f u \<le> f v) \<and>
      (\<forall> v \<in> gunodes A w. gaccepting A v \<longrightarrow> even (f v)) \<and>
      (\<forall> v \<in> gunodes A w. \<forall> r k. gurun A w r v \<longrightarrow> smap f (gtrace r v) = sconst k \<longrightarrow> odd k)"

  subsection \<open>Ranking Implies Word not in Language\<close>

  lemma ranking_stuck:
    assumes "ranking A w f"
    assumes "v \<in> gunodes A w" "gurun A w r v"
    obtains n k
    where "smap f (gtrace (sdrop n r) (gtarget (stake n r) v)) = sconst k"
  proof -
    have 0: "f u \<le> f v" if "v \<in> gunodes A w" "u \<in> gusuccessors A w v" for v u
      using assms(1) that unfolding ranking_def by auto
    have 1: "shd (v ## gtrace r v) \<in> gunodes A w" using assms(2) by auto
    have 2: "sdescending (smap f (v ## gtrace r v))"
    using 1 assms(3)
    proof (coinduction arbitrary: r v rule: sdescending.coinduct)
      case sdescending
      obtain u s where 1: "r = u ## s" using stream.exhaust by blast
      have 2: "v \<in> gunodes A w" using sdescending(1) by simp
      have 3: "gurun A w (u ## s) v" using sdescending(2) 1 by auto
      have 4: "u \<in> gusuccessors A w v" using 3 by auto
      have 5: "u \<in> gureachable A w v" using graph.reachable_successors 4 by blast
      show ?case
      unfolding 1
      proof (intro exI conjI disjI1)
        show "f u \<le> f v" using 0 2 4 by this
        show "shd (u ## gtrace s u) \<in> gunodes A w" using 2 5 by auto
        show "gurun A w s u" using 3 by auto
      qed auto
    qed
    obtain n k where 3: "sdrop n (smap f (v ## gtrace r v)) = sconst k"
      using sdescending_stuck[OF 2] by metis
    have "gtrace (sdrop (Suc n) r) (gtarget (stake (Suc n) r) v) = sdrop (Suc n) (gtrace r v)"
      using sscan_sdrop by rule
    also have "smap f \<dots> = sdrop n (smap f (v ## gtrace r v))"
      by (auto, metis 3 id_apply sdrop_smap sdrop_stl siterate.simps(2)
        sscan_const stream.map stream.map_sel(2) stream.sel(2))
    also have "\<dots> = sconst k" using 3 by this
    finally show ?thesis using that by blast
  qed

  lemma ranking_stuck_odd:
    assumes "ranking A w f"
    assumes "v \<in> gunodes A w" "gurun A w r v"
    obtains n
    where "sset (smap f (gtrace (sdrop n r) (gtarget (stake n r) v))) \<subseteq> Collect odd"
  proof -
    obtain n k where 1: "smap f (gtrace (sdrop n r) (gtarget (stake n r) v)) = sconst k"
      using ranking_stuck assms by this
    have 2: "gtarget (stake n r) v \<in> gunodes A w"
      using assms(2, 3) by (simp add: graph.nodes_target graph.run_stake)
    have 3: "gurun A w (sdrop n r) (gtarget (stake n r) v)"
      using assms(2, 3) by (simp add: graph.run_sdrop)
    have 4: "odd k" using 1 2 3 assms(1) unfolding ranking_def by meson
    have "sset (smap f (gtrace (sdrop n r) (gtarget (stake n r) v))) = sset (sconst k)"
      unfolding 1 by rule
    also have "\<dots> \<subseteq> Collect odd" using 4 by simp
    finally show ?thesis using that by simp
  qed

  lemma ranking_language:
    assumes "ranking A w f"
    shows "w \<notin> language A"
  proof
    assume 1: "w \<in> language A"
    obtain r p where 2: "run A (w ||| r) p" "p \<in> initial A" "infs (accepting A) (trace (w ||| r) p)"
      using 1 by rule
    let ?r = "fromN 1 ||| r"
    let ?v = "(0, p)"
    have 3: "?v \<in> gunodes A w" "gurun A w ?r ?v" using 2(1, 2) by (auto intro: run_grun)

    obtain n where 4: "sset (smap f (gtrace (sdrop n ?r) (gtarget (stake n ?r) ?v))) \<subseteq> {a. odd a}"
      using ranking_stuck_odd assms 3 by this
    let ?s = "stake n ?r"
    let ?t = "sdrop n ?r"
    let ?u = "gtarget ?s ?v"

    have "sset (gtrace ?t ?u) \<subseteq> gureachable A w ?v"
    proof (intro graph.reachable_trace graph.reachable_target graph.reachable.reflexive)
      show "gupath A w ?s ?v" using graph.run_stake 3(2) by this
      show "gurun A w ?t ?u" using graph.run_sdrop 3(2) by this
    qed
    also have "\<dots> \<subseteq> gunodes A w" using 3(1) by blast
    finally have 7: "sset (gtrace ?t ?u) \<subseteq> gunodes A w" by this
    have 8: "\<And> p. p \<in> gunodes A w \<Longrightarrow> gaccepting A p \<Longrightarrow> even (f p)"
      using assms unfolding ranking_def by auto
    have 9: "\<And> p. p \<in> sset (gtrace ?t ?u) \<Longrightarrow> gaccepting A p \<Longrightarrow> even (f p)" using 7 8 by auto

    have 19: "infs (accepting A) (smap snd ?r)" using 2(3) unfolding trace_alt_def by simp
    have 18: "infs (gaccepting A) ?r" using 19 by force
    have 17: "infs (gaccepting A) (gtrace ?r ?v)" using 18 unfolding gtrace_alt_def by this
    have 16: "infs (gaccepting A) (gtrace (?s @- ?t) ?v)" using 17 unfolding stake_sdrop by this
    have 15: "infs (gaccepting A) (gtrace ?t ?u)" using 16 by simp
    have 13: "infs (even \<circ> f) (gtrace ?t ?u)" using infs_mono[OF _ 15] 9 by simp
    have 12: "infs even (smap f (gtrace ?t ?u))" using 13 by simp
    have 11: "Bex (sset (smap f (gtrace ?t ?u))) even" using 12 infs_any by metis

    show False using 4 11 by auto
  qed

  subsection \<open>Word not in Language implies Ranking\<close>

  subsubsection \<open>Removal of Endangered Nodes\<close>

  definition clean :: "('label, 'state) nba \<Rightarrow> 'label stream \<Rightarrow> 'state node set \<Rightarrow> 'state node set" where
    "clean A w V \<equiv> {v \<in> V. infinite (greachable A w V v)}"

  lemma clean_decreasing: "clean A w V \<subseteq> V" unfolding clean_def by auto
  lemma clean_successors:
    assumes "v \<in> V" "u \<in> gusuccessors A w v"
    shows "u \<in> clean A w V \<Longrightarrow> v \<in> clean A w V"
  proof -
    assume 1: "u \<in> clean A w V"
    have 2: "u \<in> V" "infinite (greachable A w V u)" using 1 unfolding clean_def by auto
    have 3: "u \<in> greachable A w V v" using graph.reachable.execute assms(2) 2(1) by blast
    have 4: "greachable A w V u \<subseteq> greachable A w V v" using 3 by blast
    have 5: "infinite (greachable A w V v)" using 2(2) 4 by (simp add: infinite_super)
    show "v \<in> clean A w V" unfolding clean_def using assms(1) 5 by simp
  qed

  subsubsection \<open>Removal of Safe Nodes\<close>

  definition prune :: "('label, 'state) nba \<Rightarrow> 'label stream \<Rightarrow> 'state node set \<Rightarrow> 'state node set" where
    "prune A w V \<equiv> {v \<in> V. \<exists> u \<in> greachable A w V v. gaccepting A u}"

  lemma prune_decreasing: "prune A w V \<subseteq> V" unfolding prune_def by auto
  lemma prune_successors:
    assumes "v \<in> V" "u \<in> gusuccessors A w v"
    shows "u \<in> prune A w V \<Longrightarrow> v \<in> prune A w V"
  proof -
    assume 1: "u \<in> prune A w V"
    have 2: "u \<in> V" "\<exists> x \<in> greachable A w V u. gaccepting A x" using 1 unfolding prune_def by auto
    have 3: "u \<in> greachable A w V v" using graph.reachable.execute assms(2) 2(1) by blast
    have 4: "greachable A w V u \<subseteq> greachable A w V v" using 3 by blast
    show "v \<in> prune A w V" unfolding prune_def using assms(1) 2(2) 4 by auto
  qed

  subsubsection \<open>Run Graph Interation\<close>

  definition graph :: "('label, 'state) nba \<Rightarrow> 'label stream \<Rightarrow> nat \<Rightarrow> 'state node set" where
    "graph A w k \<equiv> alternate (clean A w) (prune A w) k (gunodes A w)"

  abbreviation "level A w k l \<equiv> {v \<in> graph A w k. fst v = l}"

  lemma graph_0[simp]: "graph A w 0 = gunodes A w" unfolding graph_def by simp
  lemma graph_Suc[simp]: "graph A w (Suc k) = (if even k then clean A w else prune A w) (graph A w k)"
    unfolding graph_def by simp

  lemma graph_antimono: "antimono (graph A w)"
    using alternate_antimono clean_decreasing prune_decreasing
    unfolding antimono_def le_fun_def graph_def
    by metis
  lemma graph_nodes: "graph A w k \<subseteq> gunodes A w" using graph_0 graph_antimono le0 antimonoD by metis
  lemma graph_successors:
    assumes "v \<in> gunodes A w" "u \<in> gusuccessors A w v"
    shows "u \<in> graph A w k \<Longrightarrow> v \<in> graph A w k"
  using assms
  proof (induct k arbitrary: u v)
    case 0
    show ?case using 0(2) by simp
  next
    case (Suc k)
    have 1: "v \<in> graph A w k" using Suc using antimono_iff_le_Suc graph_antimono rev_subsetD by blast
    show ?case using Suc(2) clean_successors[OF 1 Suc(4)] prune_successors[OF 1 Suc(4)] by auto
  qed

  lemma graph_level_finite:
    assumes "finite (nodes A)"
    shows "finite (level A w k l)"
  proof -
    have "level A w k l \<subseteq> {v \<in> gunodes A w. fst v = l}" by (simp add: graph_nodes subset_CollectI)
    also have "{v \<in> gunodes A w. fst v = l} \<subseteq> {l} \<times> nodes A" using gnodes_nodes by force
    also have "finite ({l} \<times> nodes A)" using assms(1) by simp
    finally show ?thesis by this
  qed

  lemma find_safe:
    assumes "w \<notin> language A"
    assumes "V \<noteq> {}" "V \<subseteq> gunodes A w"
    assumes "\<And> v. v \<in> V \<Longrightarrow> gsuccessors A w V v \<noteq> {}"
    obtains v
    where "v \<in> V" "\<forall> u \<in> greachable A w V v. \<not> gaccepting A u"
  proof (rule ccontr)
    assume 1: "\<not> thesis"
    have 2: "\<And> v. v \<in> V \<Longrightarrow> \<exists> u \<in> greachable A w V v. gaccepting A u" using that 1 by auto
    have 3: "\<And> r v. v \<in> initial A \<Longrightarrow> run A (w ||| r) v \<Longrightarrow> \<not> infs (accepting A) (trace (w ||| r) v)"
      using assms(1) by auto
    obtain v where 4: "v \<in> V" using assms(2) by force
    obtain x where 5: "x \<in> greachable A w V v" "gaccepting A x" using 2 4 by blast
    obtain y where 50: "gpath A w V y v" "x = gtarget y v" using 5(1) by rule
    obtain r where 6: "grun A w V r x" "infs (\<lambda> x. x \<in> V \<and> gaccepting A x) r"
    proof (rule graph.recurring_condition)
      show "x \<in> V \<and> gaccepting A x" using greachable_subset 4 5 by blast
    next
      fix v
      assume 1: "v \<in> V \<and> gaccepting A v"
      obtain v' where 20: "v' \<in> gsuccessors A w V v" using assms(4) 1 by (meson IntE equals0I)
      have 21: "v' \<in> V" using 20 by auto
      have 22: "\<exists> u \<in> greachable A w V v'. u \<in> V \<and> gaccepting A u"
        using greachable_subset 2 21 by blast
      obtain r where 30: "gpath A w V r v'" "gtarget r v' \<in> V \<and> gaccepting A (gtarget r v')"
        using 22 by blast
      show "\<exists> r. r \<noteq> [] \<and> gpath A w V r v \<and> gtarget r v \<in> V \<and> gaccepting A (gtarget r v)"
      proof (intro exI conjI)
        show "v' # r \<noteq> []" by simp
        show "gpath A w V (v' # r) v" using 20 30 by auto
        show "gtarget (v' # r) v \<in> V" using 30 by simp
        show "gaccepting A (gtarget (v' # r) v)" using 30 by simp
      qed
    qed auto
    obtain u where 100: "u \<in> ginitial A" "v \<in> gureachable A w u" using 4 assms(3) by blast
    have 101: "gupath A w y v" using gpath_subset 50(1) subset_UNIV by this
    have 102: "gurun A w r x" using grun_subset 6(1) subset_UNIV by this
    obtain t where 103: "gupath A w t u" "v = gtarget t u" using 100(2) by rule
    have 104: "gurun A w (t @- y @- r) u" using 101 102 103 50(2) by auto
    obtain s q where 7: "t @- y @- r = fromN (Suc 0) ||| s" "u = (0, q)"
      using grun_elim[OF 104] 100(1) by blast
    have 8: "run A (w ||| s) q" using grun_run[OF 104[unfolded 7]] by simp
    have 9: "q \<in> initial A" using 100(1) 7(2) by auto
    have 91: "sset (trace (w ||| s) q) \<subseteq> reachable A q"
      using nba.reachable_trace nba.reachable.reflexive 8 by this
    have 10: "\<not> infs (accepting A) (trace (w ||| s) q)" using 3 9 8 by this
    have 11: "\<not> infs (accepting A) s" using 10 unfolding trace_alt_def by simp
    have 12: "infs (gaccepting A) r" using infs_mono[OF _ 6(2)] by simp
    have "s = smap snd (t @- y @- r)" unfolding 7(1) by simp
    also have "infs (accepting A) \<dots>" using 12 by simp
    finally have 13: "infs (accepting A) s" by this
    show False using 11 13 by simp
  qed

  lemma remove_run:
    assumes "finite (nodes A)" "w \<notin> language A"
    assumes "V \<subseteq> gunodes A w" "clean A w V \<noteq> {}"
    obtains v r
    where
      "grun A w V r v"
      "sset (gtrace r v) \<subseteq> clean A w V"
      "sset (gtrace r v) \<subseteq> - prune A w (clean A w V)"
  proof -
    obtain u where 1: "u \<in> clean A w V" "\<forall> x \<in> greachable A w (clean A w V) u. \<not> gaccepting A x"
    proof (rule find_safe)
      show "w \<notin> language A" using assms(2) by this
      show "clean A w V \<noteq> {}" using assms(4) by this
      show "clean A w V \<subseteq> gunodes A w" using assms(3) by (meson clean_decreasing subset_iff)
    next
      fix v
      assume 1: "v \<in> clean A w V"
      have 2: "v \<in> V" using 1 clean_decreasing by blast
      have 3: "infinite (greachable A w V v)" using 1 clean_def by auto
      have "gsuccessors A w V v \<subseteq> gusuccessors A w v" by auto
      also have "finite \<dots>" using 2 assms(1, 3) finite_nodes_gsuccessors by blast
      finally have 4: "finite (gsuccessors A w V v)" by this
      have 5: "infinite (insert v (\<Union>((greachable A w V) ` (gsuccessors A w V v))))"
        using graph.reachable_step 3 by metis
      obtain u where 6: "u \<in> gsuccessors A w V v" "infinite (greachable A w V u)" using 4 5 by auto
      have 7: "u \<in> clean A w V" using 6 unfolding clean_def by auto
      show "gsuccessors A w (clean A w V) v \<noteq> {}" using 6(1) 7 by auto
    qed auto
    have 2: "u \<in> V" using 1(1) unfolding clean_def by auto
    have 3: "infinite (greachable A w V u)" using 1(1) unfolding clean_def by simp
    have 4: "finite (gsuccessors A w V v)" if "v \<in> greachable A w V u" for v
    proof -
      have 1: "v \<in> V" using that greachable_subset 2 by blast
      have "gsuccessors A w V v \<subseteq> gusuccessors A w v" by auto
      also have "finite \<dots>" using 1 assms(1, 3) finite_nodes_gsuccessors by blast
      finally show ?thesis by this
    qed
    obtain r where 5: "grun A w V r u" using graph.koenig[OF 3 4] by this
    have 6: "greachable A w V u \<subseteq> V" using 2 greachable_subset by blast
    have 7: "sset (gtrace r u) \<subseteq> V"
      using graph.reachable_trace[OF graph.reachable.reflexive 5(1)] 6 by blast
    have 8: "sset (gtrace r u) \<subseteq> clean A w V"
      unfolding clean_def using 7 infinite_greachable_gtrace[OF 5(1)] by auto
    have 9: "sset (gtrace r u) \<subseteq> greachable A w (clean A w V) u"
      using 5 8 by (metis graph.reachable.reflexive graph.reachable_trace grun_subset)
    show ?thesis
    proof
      show "grun A w V r u" using 5(1) by this
      show "sset (gtrace r u) \<subseteq> clean A w V" using 8 by this
      show "sset (gtrace r u) \<subseteq> - prune A w (clean A w V)"
      proof (intro subsetI ComplI)
        fix p
        assume 10: "p \<in> sset (gtrace r u)" "p \<in> prune A w (clean A w V)"
        have 20: "\<exists> x \<in> greachable A w (clean A w V) p. gaccepting A x"
          using 10(2) unfolding prune_def by auto
        have 30: "greachable A w (clean A w V) p \<subseteq> greachable A w (clean A w V) u"
          using 10(1) 9 by blast
        show "False" using 1(2) 20 30 by force
      qed
    qed
  qed

  lemma level_bounded:
    assumes "finite (nodes A)" "w \<notin> language A"
    obtains n
    where "\<And> l. l \<ge> n \<Longrightarrow> card (level A w (2 * k) l) \<le> card (nodes A) - k"
  proof (induct k arbitrary: thesis)
    case (0)
    show ?case
    proof (rule 0)
      fix l :: nat
      have "finite ({l} \<times> nodes A)" using assms(1) by simp
      also have "level A w 0 l \<subseteq> {l} \<times> nodes A" using gnodes_nodes by force
      also (card_mono) have "card \<dots> = card (nodes A)" using assms(1) by simp
      finally show "card (level A w (2 * 0) l) \<le> card (nodes A) - 0" by simp
    qed
  next
    case (Suc k)
    show ?case
    proof (cases "graph A w (Suc (2 * k)) = {}")
      case True
      have 3: "graph A w (2 * Suc k) = {}" using True prune_decreasing by simp blast
      show ?thesis using Suc(2) 3 by simp
    next
      case False
      obtain v r where 1:
        "grun A w (graph A w (2 * k)) r v"
        "sset (gtrace r v) \<subseteq> graph A w (Suc (2 * k))"
        "sset (gtrace r v) \<subseteq> - graph A w (Suc (Suc (2 * k)))"
      proof (rule remove_run)
        show "finite (nodes A)" "w \<notin> language A" using assms by this
        show "clean A w (graph A w (2 * k)) \<noteq> {}" using False by simp
        show "graph A w (2 * k) \<subseteq> gunodes A w" using graph_nodes by this
      qed auto
      obtain l q where 2: "v = (l, q)" by force
      obtain n where 90: "\<And> l. n \<le> l \<Longrightarrow> card (level A w (2 * k) l) \<le> card (nodes A) - k"
        using Suc(1) by blast
      show ?thesis
      proof (rule Suc(2))
        fix j
        assume 100: "n + Suc l \<le> j"
        have 6: "graph A w (Suc (Suc (2 * k))) \<subseteq> graph A w (Suc (2 * k))"
          using graph_antimono antimono_iff_le_Suc by blast
        have 101: "gtrace r v !! (j - Suc l) \<in> graph A w (Suc (2 * k))" using 1(2) snth_sset by auto
        have 102: "gtrace r v !! (j - Suc l) \<notin> graph A w (Suc (Suc (2 * k)))" using 1(3) snth_sset by blast
        have 103: "gtrace r v !! (j - Suc l) \<in> level A w (Suc (2 * k)) j"
          using 1(1) 100 101 2 by (auto elim: grun_elim)
        have 104: "gtrace r v !! (j - Suc l) \<notin> level A w (Suc (Suc (2 * k))) j" using 100 102 by simp
        have "level A w (2 * Suc k) j = level A w (Suc (Suc (2 * k))) j" by simp
        also have "\<dots> \<subset> level A w (Suc (2 * k)) j" using 103 104 6 by blast
        also have "\<dots> \<subseteq> level A w (2 * k) j" by (simp add: Collect_mono clean_def)
        finally have 105: "level A w (2 * Suc k) j \<subset> level A w (2 * k) j" by this
        have "card (level A w (2 * Suc k) j) < card (level A w (2 * k) j)"
          using assms(1) 105 by (simp add: graph_level_finite psubset_card_mono)
        also have "\<dots> \<le> card (nodes A) - k" using 90 100 by simp
        finally show "card (level A w (2 * Suc k) j) \<le> card (nodes A) - Suc k" by simp
      qed
    qed
  qed
  lemma graph_empty:
    assumes "finite (nodes A)" "w \<notin> language A"
    shows "graph A w (Suc (2 * card (nodes A))) = {}"
  proof -
    obtain n where 1: "\<And> l. l \<ge> n \<Longrightarrow> card (level A w (2 * card (nodes A)) l) = 0"
      using level_bounded[OF assms(1, 2), of "card (nodes A)"] by auto
    have "graph A w (2 * card (nodes A)) =
      (\<Union> l \<in> {..< n}. level A w (2 * card (nodes A)) l) \<union>
      (\<Union> l \<in> {n ..}. level A w (2 * card (nodes A)) l)"
      by auto
    also have "(\<Union> l \<in> {n ..}. level A w (2 * card (nodes A)) l) = {}"
      using graph_level_finite assms(1) 1 by fastforce
    also have "finite ((\<Union> l \<in> {..< n}. level A w (2 * card (nodes A)) l) \<union> {})"
      using graph_level_finite assms(1) by auto
    finally have 100: "finite (graph A w (2 * card (nodes A)))" by this
    have 101: "finite (greachable A w (graph A w (2 * card (nodes A))) v)" for v
      using 100 greachable_subset[of A w "graph A w (2 * card (nodes A))" v]
      using finite_insert infinite_super by auto
    show ?thesis using 101 by (simp add: clean_def)
  qed
  lemma graph_le:
    assumes "finite (nodes A)" "w \<notin> language A"
    assumes "v \<in> graph A w k"
    shows "k \<le> 2 * card (nodes A)"
    using graph_empty graph_antimono assms
    by (metis (no_types, lifting) Suc_leI antimono_def basic_trans_rules(30) empty_iff not_le_imp_less)

  subsection \<open>Node Ranks\<close>

  definition rank :: "('label, 'state) nba \<Rightarrow> 'label stream \<Rightarrow> 'state node \<Rightarrow> nat" where
    "rank A w v \<equiv> GREATEST k. v \<in> graph A w k"

  lemma rank_member:
    assumes "finite (nodes A)" "w \<notin> language A" "v \<in> gunodes A w"
    shows "v \<in> graph A w (rank A w v)"
  unfolding rank_def
  proof (rule GreatestI_nat)
    show "v \<in> graph A w 0" using assms(3) by simp
    show "\<forall> k. v \<in> graph A w k \<longrightarrow> k \<le> 2 * card (nodes A)" using graph_le assms(1, 2) by blast
  qed
  lemma rank_removed:
    assumes "finite (nodes A)" "w \<notin> language A"
    shows "v \<notin> graph A w (Suc (rank A w v))"
  proof
    assume "v \<in> graph A w (Suc (rank A w v))"
    then have 2: "Suc (rank A w v) \<le> rank A w v"
      unfolding rank_def using Greatest_le_nat graph_le assms by metis
    then show "False" by auto
  qed
  lemma rank_le:
    assumes "finite (nodes A)" "w \<notin> language A"
    assumes "v \<in> gunodes A w" "u \<in> gusuccessors A w v"
    shows "rank A w u \<le> rank A w v"
  unfolding rank_def
  proof (rule Greatest_le_nat)
    have 1: "u \<in> gureachable A w v" using graph.reachable_successors assms(4) by blast
    have 2: "u \<in> gunodes A w" using assms(3) 1 by auto
    show "v \<in> graph A w (GREATEST k. u \<in> graph A w k)"
    unfolding rank_def[symmetric]
    proof (rule graph_successors)
      show "v \<in> gunodes A w" using assms(3) by this
      show "u \<in> gusuccessors A w v" using assms(4) by this
      show "u \<in> graph A w (rank A w u)" using rank_member assms(1, 2) 2 by this
    qed
    show "\<forall> k. v \<in> graph A w k \<longrightarrow> k \<le> 2 * card (nodes A)" using graph_le assms(1, 2) by blast
  qed

  lemma language_ranking:
    assumes "finite (nodes A)" "w \<notin> language A"
    shows "ranking A w (rank A w)"
  unfolding ranking_def
  proof (intro conjI ballI allI impI)
    fix v
    assume 1: "v \<in> gunodes A w"
    have 2: "v \<in> graph A w (rank A w v)" using rank_member assms 1 by this
    show "rank A w v \<le> 2 * card (nodes A)" using graph_le assms 2 by this
  next
    fix v u
    assume 1: "v \<in> gunodes A w" "u \<in> gusuccessors A w v"
    show "rank A w u \<le> rank A w v" using rank_le assms 1 by this
  next
    fix v
    assume 1: "v \<in> gunodes A w" "gaccepting A v"
    have 2: "v \<in> graph A w (rank A w v)" using rank_member assms 1(1) by this
    have 3: "v \<notin> graph A w (Suc (rank A w v))" using rank_removed assms by this
    have 4: "v \<in> prune A w (graph A w (rank A w v))" using 2 1(2) unfolding prune_def by auto
    have 5: "graph A w (Suc (rank A w v)) \<noteq> prune A w (graph A w (rank A w v))" using 3 4 by blast
    show "even (rank A w v)" using 5 by auto
  next
    fix v r k
    assume 1: "v \<in> gunodes A w" "gurun A w r v" "smap (rank A w) (gtrace r v) = sconst k"
    have "sset (gtrace r v) \<subseteq> gureachable A w v"
      using 1(2) by (metis graph.reachable.reflexive graph.reachable_trace)
    then have 6: "sset (gtrace r v) \<subseteq> gunodes A w" using 1(1) by blast
    have 60: "rank A w ` sset (gtrace r v) \<subseteq> {k}"
      using 1(3) by (metis equalityD1 sset_sconst stream.set_map)
    have 50: "sset (gtrace r v) \<subseteq> graph A w k"
      using rank_member[OF assms] subsetD[OF 6] 60 unfolding image_subset_iff by auto
    have 70: "grun A w (graph A w k) r v" using grun_subset 1(2) 50 by this
    have 7: "sset (gtrace r v) \<subseteq> clean A w (graph A w k)"
      unfolding clean_def using 50 infinite_greachable_gtrace[OF 70] by auto
    have 8: "sset (gtrace r v) \<inter> graph A w (Suc k) = {}" using rank_removed[OF assms] 60 by blast
    have 9: "sset (gtrace r v) \<noteq> {}" using stream.set_sel(1) by auto
    have 10: "graph A w (Suc k) \<noteq> clean A w (graph A w k)" using 7 8 9 by blast
    show "odd k" using 10 unfolding graph_Suc by auto
  qed

  subsection \<open>Correctness Theorem\<close>

  theorem language_ranking_iff:
    assumes "finite (nodes A)"
    shows "w \<notin> language A \<longleftrightarrow> (\<exists> f. ranking A w f)"
    using ranking_language language_ranking assms by blast

end
