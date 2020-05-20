section \<open>Complementation\<close>

theory Complementation
imports
  "Transition_Systems_and_Automata.Maps"
  "Ranking"
begin

  subsection \<open>Level Rankings and Complementation States\<close>

  type_synonym 'state lr = "'state \<rightharpoonup> nat"

  definition lr_succ :: "('label, 'state) nba \<Rightarrow> 'label \<Rightarrow> 'state lr \<Rightarrow> 'state lr set" where
    "lr_succ A a f \<equiv> {g.
      dom g = \<Union> (transition A a ` dom f) \<and>
      (\<forall> p \<in> dom f. \<forall> q \<in> transition A a p. the (g q) \<le> the (f p)) \<and>
      (\<forall> q \<in> dom g. accepting A q \<longrightarrow> even (the (g q)))}"

  type_synonym 'state st = "'state set"

  definition st_succ :: "('label, 'state) nba \<Rightarrow> 'label \<Rightarrow> 'state lr \<Rightarrow> 'state st \<Rightarrow> 'state st" where
    "st_succ A a g P \<equiv> {q \<in> if P = {} then dom g else \<Union> (transition A a ` P). even (the (g q))}"

  type_synonym 'state cs = "'state lr \<times> 'state st"

  definition complement_succ :: "('label, 'state) nba \<Rightarrow> 'label \<Rightarrow> 'state cs \<Rightarrow> 'state cs set" where
    "complement_succ A a \<equiv> \<lambda> (f, P). {(g, st_succ A a g P) |g. g \<in> lr_succ A a f}"

  definition complement :: "('label, 'state) nba \<Rightarrow> ('label, 'state cs) nba" where
    "complement A \<equiv> nba
      (alphabet A)
      ({const (Some (2 * card (nodes A))) |` initial A} \<times> {{}})
      (complement_succ A)
      (\<lambda> (f, P). P = {})"

  lemma dom_nodes:
    assumes "fP \<in> nodes (complement A)"
    shows "dom (fst fP) \<subseteq> nodes A"
    using assms unfolding complement_def complement_succ_def lr_succ_def by (induct) (auto, blast)
  lemma ran_nodes:
    assumes "fP \<in> nodes (complement A)"
    shows "ran (fst fP) \<subseteq> {0 .. 2 * card (nodes A)}"
  using assms
  proof induct
    case (initial fP)
    show ?case
      using initial unfolding complement_def by (auto) (metis eq_refl option.inject ran_restrictD)
  next
    case (execute fP agQ)
    obtain f P where 1: "fP = (f, P)" by force
    have 2: "ran f \<subseteq> {0 .. 2 * card (nodes A)}" using execute(2) unfolding 1 by auto
    obtain a g Q where 3: "agQ = (a, (g, Q))" using prod_cases3 by this
    have 4: "p \<in> dom f \<Longrightarrow> q \<in> transition A a p \<Longrightarrow> the (g q) \<le> the (f p)" for p q
      using execute(3)
      unfolding 1 3 complement_def nba.simps complement_succ_def lr_succ_def
      by simp
    have 8: "dom g = \<Union>((transition A a) ` (dom f))"
      using execute(3)
      unfolding 1 3 complement_def nba.simps complement_succ_def lr_succ_def
      by simp
    show ?case
    unfolding 1 3 ran_def
    proof safe
      fix q k
      assume 5: "fst (snd (a, (g, Q))) q = Some k"
      have 6: "q \<in> dom g" using 5 by auto
      obtain p where 7: "p \<in> dom f" "q \<in> transition A a p" using 6 unfolding 8 by auto
      have "k = the (g q)" using 5 by auto
      also have "\<dots> \<le> the (f p)" using 4 7 by this
      also have "\<dots> \<le> 2 * card (nodes A)" using 2 7(1) by (simp add: domD ranI subset_eq)
      finally show "k \<in> {0 .. 2 * card (nodes A)}" by auto
    qed
  qed
  lemma states_nodes:
    assumes "fP \<in> nodes (complement A)"
    shows "snd fP \<subseteq> nodes A"
  using assms
  proof induct
    case (initial fP)
    show ?case using initial unfolding complement_def by auto
  next
    case (execute fP agQ)
    obtain f P where 1: "fP = (f, P)" by force
    have 2: "P \<subseteq> nodes A" using execute(2) unfolding 1 by auto
    obtain a g Q where 3: "agQ = (a, (g, Q))" using prod_cases3 by this
    have 11: "a \<in> alphabet A" using execute(3) unfolding 3 complement_def by auto
    have 10: "(g, Q) \<in> nodes (complement A)" using execute(1, 3) unfolding 1 3 by auto
    have 4: "dom g \<subseteq> nodes A" using dom_nodes[OF 10] by simp
    have 5: "\<Union> (transition A a ` P) \<subseteq> nodes A" using 2 11 by auto
    have 6: "Q \<subseteq> nodes A"
      using execute(3)
      unfolding 1 3 complement_def nba.simps complement_succ_def st_succ_def
      using 4 5
      by (auto split: if_splits)
    show ?case using 6 unfolding 3 by auto
  qed

  theorem complement_finite:
    assumes "finite (nodes A)"
    shows "finite (nodes (complement A))"
  proof -
    let ?lrs = "{f. dom f \<subseteq> nodes A \<and> ran f \<subseteq> {0 .. 2 * card (nodes A)}}"
    have 1: "finite ?lrs" using finite_set_of_finite_maps' assms by auto
    let ?states = "Pow (nodes A)"
    have 2: "finite ?states" using assms by simp
    have "nodes (complement A) \<subseteq> ?lrs \<times> ?states" by (force dest: dom_nodes ran_nodes states_nodes)
    also have "finite \<dots>" using 1 2 by simp
    finally show ?thesis by this
  qed

  lemma complement_trace_snth:
    assumes "run (complement A) (w ||| r) p"
    defines "m \<equiv> p ## trace (w ||| r) p"
    obtains
      "fst (m !! Suc k) \<in> lr_succ A (w !! k) (fst (m !! k))"
      "snd (m !! Suc k) = st_succ A (w !! k) (fst (m !! Suc k)) (snd (m !! k))"
  proof
    have 1: "r !! k \<in> transition (complement A) (w !! k) (m !! k)" using nba.run_snth assms by force
    show "fst (m !! Suc k) \<in> lr_succ A (w !! k) (fst (m !! k))"
      using assms(2) 1 unfolding complement_def complement_succ_def nba.trace_alt_def by auto
    show "snd (m !! Suc k) = st_succ A (w !! k) (fst (m !! Suc k)) (snd (m !! k))"
      using assms(2) 1 unfolding complement_def complement_succ_def nba.trace_alt_def by auto
  qed

  subsection \<open>Word in Complement Language Implies Ranking\<close>

  lemma complement_ranking:
    assumes "w \<in> language (complement A)"
    obtains f
    where "ranking A w f"
  proof -
    obtain r p where 1:
      "run (complement A) (w ||| r) p"
      "p \<in> initial (complement A)"
      "infs (accepting (complement A)) (p ## r)"
      using assms by rule
    let ?m = "p ## r"
    obtain 100:
      "fst (?m !! Suc k) \<in> lr_succ A (w !! k) (fst (?m !! k))"
      "snd (?m !! Suc k) = st_succ A (w !! k) (fst (?m !! Suc k)) (snd (?m !! k))"
      for k using complement_trace_snth 1(1) unfolding nba.trace_alt_def szip_smap_snd by metis
    define f where "f \<equiv> \<lambda> (k, q). the (fst (?m !! k) q)"
    define P where "P k \<equiv> snd (?m !! k)" for k
    have 2: "snd v \<in> dom (fst (?m !! fst v))" if "v \<in> gunodes A w" for v
    using that
    proof induct
      case (initial v)
      then show ?case using 1(2) unfolding complement_def by auto
    next
      case (execute v u)
      have "snd u \<in> \<Union> ((transition A (w !! fst v)) ` (dom (fst (?m !! fst v))))"
        using execute(2, 3) by auto
      also have "\<dots> = dom (fst (?m !! Suc (fst v)))"
        using 100 unfolding lr_succ_def by simp
      also have "Suc (fst v) = fst u" using execute(3) by auto
      finally show ?case by this
    qed
    have 3: "f u \<le> f v" if 10: "v \<in> gunodes A w" and 11: "u \<in> gusuccessors A w v" for u v
    proof -
      have 15: "snd u \<in> transition A (w !! fst v) (snd v)" using 11 by auto
      have 16: "snd v \<in> dom (fst (?m !! fst v))" using 2 10 by this
      have "f u = the (fst (?m !! fst u) (snd u))" unfolding f_def by (simp add: case_prod_beta)
      also have "fst u = Suc (fst v)" using 11 by auto
      also have "the (fst (?m !! \<dots>) (snd u)) \<le> the (fst (?m !! fst v) (snd v))"
        using 100 15 16 unfolding lr_succ_def by auto
      also have "\<dots> = f v" unfolding f_def by (simp add: case_prod_beta)
      finally show "f u \<le> f v" by this
    qed
    have 4: "\<exists> l \<ge> k. P l = {}" for k
    proof -
      have 15: "infs (\<lambda> (k, P). P = {}) ?m" using 1(3) unfolding complement_def by auto
      obtain l where 17: "l \<ge> k" "snd (?m !! l) = {}" using 15 unfolding infs_snth by force
      have 19: "P l = {}" unfolding P_def using 17 by auto
      show ?thesis using 19 17(1) by auto
    qed
    show ?thesis
    proof (rule that, unfold ranking_def, intro conjI ballI impI allI)
      fix v
      assume "v \<in> gunodes A w"
      then show "f v \<le> 2 * card (nodes A)"
      proof induct
        case (initial v)
        then show ?case using 1(2) unfolding complement_def f_def by auto
      next
        case (execute v u)
        have "f u \<le> f v" using 3[OF execute(1)] execute(3) by simp
        also have "\<dots> \<le> 2 * card (nodes A)" using execute(2) by this
        finally show ?case by this
      qed
    next
      fix v u
      assume 10: "v \<in> gunodes A w"
      assume 11: "u \<in> gusuccessors A w v"
      show "f u \<le> f v" using 3 10 11 by this
    next
      fix v
      assume 10: "v \<in> gunodes A w"
      assume 11: "gaccepting A v"
      show "even (f v)"
      using 10
      proof cases
        case (initial)
        then show ?thesis using 1(2) unfolding complement_def f_def by auto
      next
        case (execute u)
        have 12: "snd v \<in> dom (fst (?m !! fst v))" using execute graph.nodes.execute 2 by blast
        have 12: "snd v \<in> dom (fst (?m !! Suc (fst u)))" using 12 execute(2) by auto
        have 13: "accepting A (snd v)" using 11 by auto
        have "f v = the (fst (?m !! fst v) (snd v))" unfolding f_def by (simp add: case_prod_beta)
        also have "fst v = Suc (fst u)" using execute(2) by auto
        also have "even (the (fst (?m !! Suc (fst u)) (snd v)))"
          using 100 12 13 unfolding lr_succ_def by simp
        finally show ?thesis by this
      qed
    next
      fix v s k
      assume 10: "v \<in> gunodes A w"
      assume 11: "gurun A w s v"
      assume 12: "smap f (gtrace s v) = sconst k"
      show "odd k"
      proof
        assume 13: "even k"
        obtain t u where 14: "u \<in> ginitial A" "gupath A w t u" "v = gtarget t u" using 10 by auto
        obtain l where 15: "l \<ge> length t" "P l = {}" using 4 by auto
        obtain l' where 16: "l' \<ge> Suc l" "P l' = {}" using 4 by auto
        have 30: "gurun A w (t @- s) u" using 11 14 by auto
        have 21: "fst (gtarget (stake (Suc l) (t @- s)) u) = Suc l" for l
          unfolding sscan_snth[symmetric] using 30 14(1) by (auto elim!: grun_elim)
        have 17: "snd (gtarget (stake (Suc l + i) (t @- s)) u) \<in> P (Suc l + i)" for i
        proof (induct i)
          case (0)
          have 20: "gtarget (stake (Suc l) (t @- s)) u \<in> gunodes A w"
            using 14 11 by (force simp add: 15(1) le_SucI graph.run_stake stake_shift)
          have "snd (gtarget (stake (Suc l) (t @- s)) u) \<in>
            dom (fst (?m !! fst (gtarget (stake (Suc l) (t @- s)) u)))"
            using 2[OF 20] by this
          also have "fst (gtarget (stake (Suc l) (t @- s)) u) = Suc l" using 21 by this
          finally have 22: "snd (gtarget (stake (Suc l) (t @- s)) u) \<in> dom (fst (?m !! Suc l))" by this
          have "gtarget (stake (Suc l) (t @- s)) u = gtrace (t @- s) u !! l" unfolding sscan_snth by rule
          also have "\<dots> = gtrace s v !! (l - length t)" using 15(1) by simp
          also have "f \<dots> = smap f (gtrace s v) !! (l - length t)" by simp
          also have "smap f (gtrace s v) = sconst k" unfolding 12 by rule
          also have "sconst k !! (l - length t) = k" by simp
          finally have 23: "even (f (gtarget (stake (Suc l) (t @- s)) u))" using 13 by simp
          have 24: "snd (gtarget (stake (Suc l) (t @- s)) u) \<in>
            {p \<in> dom (fst (?m !! Suc l)). even (f (Suc l, p))}"
            using 21 22 23 by (metis (mono_tags, lifting) mem_Collect_eq prod.collapse)
          also have "\<dots> = st_succ A (w !! l) (fst (?m !! Suc l)) (P l)"
            unfolding 15(2) st_succ_def f_def by simp
          also have "\<dots> = P (Suc l)" using 100(2) unfolding P_def by rule
          also have "P (Suc l) = P (l + Suc 0)" by simp
          finally show ?case by auto
        next
          case (Suc i)
          have 20: "P (Suc l + i) \<noteq> {}" using Suc by auto
          have 21: "fst (gtarget (stake (Suc l + Suc i) (t @- s)) u) = Suc l + Suc i"
            using 21 by (simp add: stake_shift)
          have "gtarget (stake (Suc l + Suc i) (t @- s)) u = gtrace (t @- s) u !! (l + Suc i)"
            unfolding sscan_snth by simp
          also have "\<dots> \<in> gusuccessors A w (gtarget (stake (Suc (l + i)) (t @- s)) u)"
            using graph.run_snth[OF 30, of "l + Suc i"] by simp
          finally have 220: "snd (gtarget (stake (Suc (Suc l + i)) (t @- s)) u) \<in>
              transition A (w !! (Suc l + i)) (snd (gtarget (stake (Suc (l + i)) (t @- s)) u))"
            using 21 by auto
          have 22: "snd (gtarget (stake (Suc l + Suc i) (t @- s)) u) \<in>
            \<Union> (transition A (w !! (Suc l + i)) ` P (Suc l + i))" using 220 Suc by auto
          have "gtarget (stake (Suc l + Suc i) (t @- s)) u = gtrace (t @- s) u !! (l + Suc i)"
            unfolding sscan_snth by simp
          also have "\<dots> = gtrace s v !! (l + Suc i - length t)" using 15(1)
            by (metis add.commute shift_snth_ge sscan_const trans_le_add2)
          also have "f \<dots> = smap f (gtrace s v) !! (l + Suc i - length t)" by simp
          also have "smap f (gtrace s v) = sconst k" unfolding 12 by rule
          also have "sconst k !! (l + Suc i - length t) = k" by simp
          finally have 23: "even (f (gtarget (stake (Suc l + Suc i) (t @- s)) u))" using 13 by auto
          have "snd (gtarget (stake (Suc l + Suc i) (t @- s)) u) \<in>
            {p \<in> \<Union> (transition A (w !! (Suc l + i)) ` P (Suc l + i)). even (f (Suc (Suc l + i), p))}"
            using 21 22 23 by (metis (mono_tags) add_Suc_right mem_Collect_eq prod.collapse)
          also have "\<dots> = st_succ A (w !! (Suc l + i)) (fst (?m !! Suc (Suc l + i))) (P (Suc l + i))"
            unfolding st_succ_def f_def using 20 by simp
          also have "\<dots> = P (Suc (Suc l + i))" unfolding 100(2)[folded P_def] by rule
          also have "\<dots> = P (Suc l + Suc i)" by simp
          finally show ?case by this
        qed
        show "False" using 16 17 using nat_le_iff_add by auto
      qed
    qed
  qed

  subsection \<open>Ranking Implies Word in Complement Language\<close>

  definition reach where
    "reach A w i \<equiv> {target r p |r p. path A r p \<and> p \<in> initial A \<and> map fst r = stake i w}"

  lemma reach_0[simp]: "reach A w 0 = initial A" unfolding reach_def by auto
  lemma reach_Suc_empty:
    assumes "w !! n \<notin> alphabet A"
    shows "reach A w (Suc n) = {}"
  proof safe
    fix q
    assume 1: "q \<in> reach A w (Suc n)"
    obtain r p where 2: "q = target r p" "path A r p" "p \<in> initial A" "map fst r = stake (Suc n) w"
      using 1 unfolding reach_def by blast
    have 3: "path A (take n r @ drop n r) p" using 2(2) by simp
    have 4: "map fst r = stake n w @ [w !! n]" using 2(4) stake_Suc by auto
    have 5: "map snd r = take n (map snd r) @ [q]" using 2(1, 4) 4
      by (metis One_nat_def Suc_inject Suc_neq_Zero Suc_pred append.right_neutral
        append_eq_conv_conj drop_map id_take_nth_drop last_ConsR last_conv_nth length_0_conv
        length_map length_stake lessI nba.target_alt_def nba.states_alt_def zero_less_Suc)
    have 6: "drop n r = [(w !! n, q)]" using 4 5
      by (metis append_eq_conv_conj append_is_Nil_conv append_take_drop_id drop_map
        length_greater_0_conv length_stake stake_cycle_le stake_invert_Nil
        take_map zip_Cons_Cons zip_map_fst_snd)
    show "q \<in> {}" using assms 3 unfolding 6 by auto
  qed
  lemma reach_Suc_succ:
    assumes "w !! n \<in> alphabet A"
    shows "reach A w (Suc n) = \<Union>((transition A (w !! n) ` (reach A w n)))"
  proof safe
    fix q
    assume 1: "q \<in> reach A w (Suc n)"
    obtain r p where 2: "q = target r p" "path A r p" "p \<in> initial A" "map fst r = stake (Suc n) w"
      using 1 unfolding reach_def by blast
    have 3: "path A (take n r @ drop n r) p" using 2(2) by simp
    have 4: "map fst r = stake n w @ [w !! n]" using 2(4) stake_Suc by auto
    have 5: "map snd r = take n (map snd r) @ [q]" using 2(1, 4) 4
      by (metis One_nat_def Suc_inject Suc_neq_Zero Suc_pred append.right_neutral
        append_eq_conv_conj drop_map id_take_nth_drop last_ConsR last_conv_nth length_0_conv
        length_map length_stake lessI nba.target_alt_def nba.states_alt_def zero_less_Suc)
    have 6: "drop n r = [(w !! n, q)]" using 4 5
      by (metis append_eq_conv_conj append_is_Nil_conv append_take_drop_id drop_map
        length_greater_0_conv length_stake stake_cycle_le stake_invert_Nil
        take_map zip_Cons_Cons zip_map_fst_snd)
    show "q \<in> \<Union>((transition A (w !! n) ` (reach A w n)))"
    unfolding reach_def
    proof (intro UN_I CollectI exI conjI)
      show "target (take n r) p = target (take n r) p" by rule
      show "path A (take n r) p" using 3 by blast
      show "p \<in> initial A" using 2(3) by this
      show "map fst (take n r) = stake n w" using 2 by (metis length_stake lessI nat.distinct(1)
        stake_cycle_le stake_invert_Nil take_map take_stake)
      show "q \<in> transition A (w !! n) (target (take n r) p)" using 3 unfolding 6 by auto
    qed
  next
    fix p q
    assume 1: "p \<in> reach A w n" "q \<in> transition A (w !! n) p"
    obtain r x where 2: "p = target r x" "path A r x" "x \<in> initial A" "map fst r = stake n w"
      using 1(1) unfolding reach_def by blast
    show "q \<in> reach A w (Suc n)"
    unfolding reach_def
    proof (intro CollectI exI conjI)
      show "q = target (r @ [(w !! n, q)]) x" using 1 2 by auto
      show "path A (r @ [(w !! n, q)]) x" using assms 1(2) 2(1, 2) by auto
      show "x \<in> initial A" using 2(3) by this
      show "map fst (r @ [(w !! n, q)]) = stake (Suc n) w" using 1 2
        by (metis eq_fst_iff list.simps(8) list.simps(9) map_append stake_Suc)
    qed
  qed
  lemma reach_Suc[simp]: "reach A w (Suc n) = (if w !! n \<in> alphabet A
    then \<Union>((transition A (w !! n) ` (reach A w n))) else {})"
    using reach_Suc_empty reach_Suc_succ by metis
  lemma reach_nodes: "reach A w i \<subseteq> nodes A" by (induct i) (auto)
  lemma reach_gunodes: "{i} \<times> reach A w i \<subseteq> gunodes A w"
    by (induct i) (auto intro: graph.nodes.execute)

  lemma ranking_complement:
    assumes "finite (nodes A)" "w \<in> streams (alphabet A)" "ranking A w f"
    shows "w \<in> language (complement A)"
  proof -
    define f' where "f' \<equiv> \<lambda> (k, p). if k = 0 then 2 * card (nodes A) else f (k, p)"
    have 0: "ranking A w f'"
    unfolding ranking_def
    proof (intro conjI ballI impI allI)
      show "\<And> v. v \<in> gunodes A w \<Longrightarrow> f' v \<le> 2 * card (nodes A)"
        using assms(3) unfolding ranking_def f'_def by auto
      show "\<And> v u. v \<in> gunodes A w \<Longrightarrow> u \<in> gusuccessors A w v \<Longrightarrow> f' u \<le> f' v"
        using assms(3) unfolding ranking_def f'_def by fastforce
      show "\<And> v. v \<in> gunodes A w \<Longrightarrow> gaccepting A v \<Longrightarrow> even (f' v)"
        using assms(3) unfolding ranking_def f'_def by auto
    next
      have 1: "v \<in> gunodes A w \<Longrightarrow> gurun A w r v \<Longrightarrow> smap f (gtrace r v) = sconst k \<Longrightarrow> odd k"
        for v r k using assms(3) unfolding ranking_def by meson
      fix v r k
      assume 2: "v \<in> gunodes A w" "gurun A w r v" "smap f' (gtrace r v) = sconst k"
      have 20: "shd r \<in> gureachable A w v" using 2
        by (auto) (metis graph.reachable.reflexive graph.reachable_trace gtrace_alt_def subsetD shd_sset)
      obtain 3:
        "shd r \<in> gunodes A w"
        "gurun A w (stl r) (shd r)"
        "smap f' (gtrace (stl r) (shd r)) = sconst k"
        using 2 20 by (metis (no_types, lifting) eq_id_iff graph.nodes_trans graph.run_scons_elim
          siterate.simps(2) sscan.simps(2) stream.collapse stream.map_sel(2))
      have 4: "k \<noteq> 0" if "(k, p) \<in> sset r" for k p
      proof -
        obtain ra ka pa where 1: "r = fromN (Suc ka) ||| ra" "v = (ka, pa)"
          using grun_elim[OF 2(2)] by this
        have 2: "k \<in> sset (fromN (Suc ka))" using 1(1) that
          by (metis image_eqI prod.sel(1) szip_smap_fst stream.set_map)
        show ?thesis using 2 by simp
      qed
      have 5: "smap f' (gtrace (stl r) (shd r)) = smap f (gtrace (stl r) (shd r))"
      proof (rule stream.map_cong)
        show "gtrace (stl r) (shd r) = gtrace (stl r) (shd r)" by rule
      next
        fix z
        assume 1: "z \<in> sset (gtrace (stl r) (shd r))"
        have 2: "fst z \<noteq> 0" using 4 1 by (metis gtrace_alt_def prod.collapse stl_sset)
        show "f' z = f z" using 2 unfolding f'_def by (auto simp: case_prod_beta)
      qed
      show "odd k" using 1 3 5 by simp
    qed

    define g where "g i p \<equiv> if p \<in> reach A w i then Some (f' (i, p)) else None" for i p
    have g_dom[simp]: "dom (g i) = reach A w i" for i
      unfolding g_def by (auto) (metis option.simps(3))
    have g_0[simp]: "g 0 = const (Some (2 * card (nodes A))) |` initial A"
      unfolding g_def f'_def by auto
    have g_Suc[simp]: "g (Suc n) \<in> lr_succ A (w !! n) (g n)" for n
    unfolding lr_succ_def
    proof (intro CollectI conjI ballI impI)
      show "dom (g (Suc n)) = \<Union> (transition A (w !! n) ` dom (g n))" using snth_in assms(2) by auto
    next
      fix p q
      assume 100: "p \<in> dom (g n)" "q \<in> transition A (w !! n) p"
      have 101: "q \<in> reach A w (Suc n)" using snth_in assms(2) 100 by auto
      have 102: "(n, p) \<in> gunodes A w" using 100(1) reach_gunodes g_dom by blast
      have 103: "(Suc n, q) \<in> gusuccessors A w (n, p)" using snth_in assms(2) 102 100(2) by auto
      have 104: "p \<in> reach A w n" using 100(1) by simp
      have "g (Suc n) q = Some (f' (Suc n, q))" using 101 unfolding g_def by simp
      also have "the \<dots> = f' (Suc n, q)" by simp
      also have "\<dots> \<le> f' (n, p)" using 0 unfolding ranking_def using 102 103 by simp
      also have "\<dots> = the (Some (f' (n, p)))" by simp
      also have "Some (f' (n, p)) = g n p" using 104 unfolding g_def by simp
      finally show "the (g (Suc n) q) \<le> the (g n p)" by this
    next
      fix p
      assume 100: "p \<in> dom (g (Suc n))" "accepting A p"
      have 101: "p \<in> reach A w (Suc n)" using 100(1) by simp
      have 102: "(Suc n, p) \<in> gunodes A w" using 101 reach_gunodes by blast
      have 103: "gaccepting A (Suc n, p)" using 100(2) by simp
      have "the (g (Suc n) p) = f' (Suc n, p)" using 101 unfolding g_def by simp
      also have "even \<dots>" using 0 unfolding ranking_def using 102 103 by auto
      finally show "even (the (g (Suc n) p))" by this
    qed

    define P where "P \<equiv> rec_nat {} (\<lambda> n. st_succ A (w !! n) (g (Suc n)))"
    have P_0[simp]: "P 0 = {}" unfolding P_def by simp
    have P_Suc[simp]: "P (Suc n) = st_succ A (w !! n) (g (Suc n)) (P n)" for n
      unfolding P_def by simp
    have P_reach: "P n \<subseteq> reach A w n" for n
      using snth_in assms(2) by (induct n) (auto simp add: st_succ_def)
    have "P n \<subseteq> reach A w n" for n using P_reach by auto
    also have "\<dots> n \<subseteq> nodes A" for n using reach_nodes by this
    also have "finite (nodes A)" using assms(1) by this
    finally have P_finite: "finite (P n)" for n by this

    define s where "s \<equiv> smap g nats ||| smap P nats"

    show ?thesis
    proof
      show "run (complement A) (w ||| stl s) (shd s)"
      proof (intro nba.snth_run conjI, simp_all del: stake.simps stake_szip)
        fix k
        show "w !! k \<in> alphabet (complement A)" using snth_in assms(2) unfolding complement_def by auto
        have "stl s !! k = s !! Suc k" by simp
        also have "\<dots> \<in> complement_succ A (w !! k) (s !! k)"
          unfolding complement_succ_def s_def using P_Suc by simp
        also have "\<dots> = complement_succ A (w !! k) (target (stake k (w ||| stl s)) (shd s))"
          unfolding sscan_scons_snth[symmetric] nba.trace_alt_def by simp
        also have "\<dots> = transition (complement A) (w !! k) (target (stake k (w ||| stl s)) (shd s))"
          unfolding complement_def nba.sel by rule
        finally show "stl s !! k \<in>
          transition (complement A) (w !! k) (target (stake k (w ||| stl s)) (shd s))" by this
      qed
      show "shd s \<in> initial (complement A)" unfolding complement_def s_def using P_0 by simp
      show "infs (accepting (complement A)) (shd s ## stl s)"
      proof -
        have 10: "\<forall> n. \<exists> k \<ge> n. P k = {}"
        proof (rule ccontr)
          assume 20: "\<not> (\<forall> n. \<exists> k \<ge> n. P k = {})"
          obtain k where 22: "P (k + n) \<noteq> {}" for n using 20 using le_add1 by blast
          define m where "m n S \<equiv> {p \<in> \<Union>((transition A (w !! n) ` S)). even (the (g (Suc n) p))}" for n S
          define R where "R i n S \<equiv> rec_nat S (\<lambda> i. m (n + i)) i" for i n S
          have R_0[simp]: "R 0 n = id" for n unfolding R_def by auto
          have R_Suc[simp]: "R (Suc i) n = m (n + i) \<circ> R i n" for i n unfolding R_def by auto
          have R_Suc': "R (Suc i) n = R i (Suc n) \<circ> m n" for i n unfolding R_Suc by (induct i) (auto)
          have R_reach: "R i n S \<subseteq> reach A w (n + i)" if "S \<subseteq> reach A w n" for i n S
            using snth_in assms(2) that m_def by (induct i) (auto)
          have P_R: "P (k + i) = R i k (P k)" for i
            using 22 by (induct i) (auto simp add: case_prod_beta' m_def st_succ_def)

          have 50: "R i n S = (\<Union> p \<in> S. R i n {p})" for i n S
            by (induct i) (auto simp add: m_def prod.case_eq_if)
          have 51: "R (i + j) n S = {}" if "R i n S = {}" for i j n S
            using that by (induct j) (auto simp add: m_def prod.case_eq_if)
          have 52: "R j n S = {}" if "i \<le> j" "R i n S = {}" for i j n S
            using 51 by (metis le_add_diff_inverse that(1) that(2))

          have 1: "\<exists> p \<in> S. \<forall> i. R i n {p} \<noteq> {}"
            if assms: "finite S" "\<And> i. R i n S \<noteq> {}" for n S
          proof (rule ccontr)
            assume 1: "\<not> (\<exists> p \<in> S. \<forall> i. R i n {p} \<noteq> {})"
            obtain f where 3: "\<And> p. p \<in> S \<Longrightarrow> R (f p) n {p} = {}" using 1 by metis
            have 4: "R (Sup (f ` S)) n {p} = {}" if "p \<in> S" for p
            proof (rule 52)
              show "f p \<le> Sup (f ` S)" using assms(1) that by (auto intro: le_cSup_finite)
              show "R (f p) n {p} = {}" using 3 that by this
            qed
            have "R (Sup (f ` S)) n S = (\<Union> p \<in> S. R (Sup (f ` S)) n {p})" using 50 by this
            also have "\<dots> = {}" using 4 by simp
            finally have 5: "R (Sup (f ` S)) n S = {}" by this
            show "False" using that(2) 5 by auto
          qed
          have 2: "\<And> i. R i (k + 0) (P k) \<noteq> {}" using 22 P_R by simp
          obtain p where 3: "p \<in> P k" "\<And> i. R i k {p} \<noteq> {}" using 1[OF P_finite 2] by auto

          define Q where "Q n p \<equiv> (\<forall> i. R i (k + n) {p} \<noteq> {}) \<and> p \<in> P (k + n)" for n p
          have 5: "\<exists> q \<in> transition A (w !! (k + n)) p. Q (Suc n) q" if "Q n p" for n p
          proof -
            have 11: "p \<in> P (k + n)" "\<And> i. R i (k + n) {p} \<noteq> {}" using that unfolding Q_def by auto
            have 12: "R (Suc i) (k + n) {p} \<noteq> {}" for i using 11(2) by this
            have 13: "R i (k + Suc n) (m (k + n) {p}) \<noteq> {}" for i using 12 unfolding R_Suc' by simp
            have "{p} \<subseteq> P (k + n)" using 11(1) by auto
            also have "\<dots> \<subseteq> reach A w (k + n)" using P_reach by this
            finally have "R 1 (k + n) {p} \<subseteq> reach A w (k + n + 1)" using R_reach by blast
            also have "\<dots> \<subseteq> nodes A" using reach_nodes by this
            also have "finite (nodes A)" using assms(1) by this
            finally have 14: "finite (m (k + n) {p})" by simp
            obtain q where 14: "q \<in> m (k + n) {p}" "\<And> i. R i (k + Suc n) {q} \<noteq> {}"
              using 1[OF 14 13] by auto
            show ?thesis
            unfolding Q_def prod.case
            proof (intro bexI conjI allI)
              show "\<And> i. R i (k + Suc n) {q} \<noteq> {}" using 14(2) by this
              show "q \<in> P (k + Suc n)"
                using 14(1) 11(1) 22 unfolding m_def by (auto simp add: st_succ_def)
              show "q \<in> transition A (w !! (k + n)) p" using 14(1) unfolding m_def by simp
            qed
          qed
          obtain r where 23:
            "run A r p" "\<And> i. Q i ((p ## trace r p) !! i)" "\<And> i. fst (r !! i) = w !! (k + i)"
          proof (rule nba.invariant_run_index[of Q 0 p A "\<lambda> n p a. fst a = w !! (k + n)"])
            show "Q 0 p" unfolding Q_def using 3 by auto
            show "\<exists> a. (fst a \<in> alphabet A \<and> snd a \<in> transition A (fst a) p) \<and>
              Q (Suc n) (snd a) \<and> fst a = w !! (k + n)" if "Q n p" for n p
              using snth_in assms(2) 5 that by fastforce
          qed auto
          have 20: "smap fst r = sdrop k w" using 23(3) by (intro eqI_snth) (simp add: case_prod_beta)
          have 21: "(p ## smap snd r) !! i \<in> P (k + i)" for i
            using 23(2) unfolding Q_def unfolding nba.trace_alt_def by simp
          obtain r where 23: "run A (sdrop k w ||| stl r) (shd r)" "\<And> i. r !! i \<in> P (k + i)"
            using 20 21 23(1) by (metis stream.sel(1) stream.sel(2) szip_smap)
          let ?v = "(k, shd r)"
          let ?r = "fromN (Suc k) ||| stl r"
          have "shd r = r !! 0" by simp
          also have "\<dots> \<in> P k" using 23(2)[of 0] by simp
          also have "\<dots> \<subseteq> reach A w k" using P_reach by this
          finally have 24: "?v \<in> gunodes A w" using reach_gunodes by blast
          have 25: "gurun A w ?r ?v" using run_grun 23(1) by this
          obtain l where 26: "sset (smap f' (gtrace (sdrop l ?r) (gtarget (stake l ?r) ?v))) \<subseteq>
            Collect odd" using ranking_stuck_odd 0 24 25 by this
          have 27: "f' (Suc (k + l), r !! Suc l) =
            shd (smap f' (gtrace (sdrop l ?r) (gtarget (stake l ?r) ?v)))" by (simp add: algebra_simps)
          also have "\<dots> \<in> sset (smap f' (gtrace (sdrop l ?r) (gtarget (stake l ?r) ?v)))"
            using shd_sset by this
          also have "\<dots> \<subseteq> Collect odd" using 26 by this
          finally have 28: "odd (f' (Suc (k + l), r !! Suc l))" by simp
          have "r !! Suc l \<in> P (Suc (k + l))" using 23(2) by (metis add_Suc_right)
          also have "\<dots> = {p \<in> \<Union> (transition A (w !! (k + l)) ` P (k + l)).
            even (the (g (Suc (k + l)) p))}" using 23(2) by (auto simp: st_succ_def)
          also have "\<dots> \<subseteq> {p. even (the (g (Suc (k + l)) p))}" by auto
          finally have 29: "even (the (g (Suc (k + l)) (r !! Suc l)))" by auto
          have 30: "r !! Suc l \<in> reach A w (Suc (k + l))"
            using 23(2) P_reach by (metis add_Suc_right subsetCE)
          have 31: "even (f' (Suc (k + l), r !! Suc l))" using 29 30 unfolding g_def by simp
          show "False" using 28 31 by simp
        qed
        have 11: "infs (\<lambda> k. P k = {}) nats" using 10 unfolding infs_snth by simp
        have "infs (\<lambda> S. S = {}) (smap snd (smap g nats ||| smap P nats))"
          using 11 by (simp add: comp_def)
        then have "infs (\<lambda> x. snd x = {}) (smap g nats ||| smap P nats)"
          by (simp add: comp_def del: szip_smap_snd)
        then have "infs (\<lambda> (f, P). P = {}) (smap g nats ||| smap P nats)" 
          by (simp add: case_prod_beta')
        then have "infs (\<lambda> (f, P). P = {}) (stl (smap g nats ||| smap P nats))" by blast
        then have "infs (\<lambda> (f, P). P = {}) (smap snd (w ||| stl (smap g nats ||| smap P nats)))" by simp
        then have "infs (\<lambda> (f, P). P = {}) (stl s)" unfolding s_def by simp
        then show ?thesis unfolding complement_def by auto
      qed
    qed
  qed

  subsection \<open>Correctness Theorem\<close>

  theorem complement_language:
    assumes "finite (nodes A)"
    shows "language (complement A) = streams (alphabet A) - language A"
  proof (safe del: notI)
    have 1: "alphabet (complement A) = alphabet A" unfolding complement_def nba.sel by rule
    show "w \<in> streams (alphabet A)" if "w \<in> language (complement A)" for w
      using nba.language_alphabet that 1 by force
    show "w \<notin> language A" if "w \<in> language (complement A)" for w
      using complement_ranking ranking_language that by metis
    show "w \<in> language (complement A)" if "w \<in> streams (alphabet A)" "w \<notin> language A" for w
      using language_ranking ranking_complement assms that by blast
  qed

end
