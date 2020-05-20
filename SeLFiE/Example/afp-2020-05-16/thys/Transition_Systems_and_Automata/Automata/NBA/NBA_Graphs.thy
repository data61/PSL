section \<open>Connecting Nondeterministic Büchi Automata to CAVA Automata Structures\<close>

theory NBA_Graphs
imports
  NBA
  CAVA_Automata.Automata_Impl
begin

  no_notation build (infixr "##" 65)

  subsection \<open>Regular Graphs\<close>

  definition nba_g :: "('label, 'state) nba \<Rightarrow> 'state graph_rec" where
    "nba_g A \<equiv> \<lparr> g_V = UNIV, g_E = E_of_succ (successors A), g_V0 = initial A \<rparr>"

  lemma nba_g_graph[simp]: "graph (nba_g A)" unfolding nba_g_def graph_def by simp

  lemma nba_g_V0: "g_V0 (nba_g A) = initial A" unfolding nba_g_def by simp
  lemma nba_g_E_rtrancl: "(g_E (nba_g A))\<^sup>* = {(p, q). q \<in> reachable A p}"
  unfolding nba_g_def graph_rec.simps E_of_succ_def
  proof safe
    show "(p, q) \<in> {(p, q). q \<in> successors A p}\<^sup>*" if "q \<in> reachable A p" for p q
      using that by (induct) (auto intro: rtrancl_into_rtrancl)
    show "q \<in> reachable A p" if "(p, q) \<in> {(p, q). q \<in> successors A p}\<^sup>*" for p q
      using that by induct auto
  qed

  lemma nba_g_rtrancl_path: "(g_E (nba_g A))\<^sup>* = {(p, target r p) |r p. NBA.path A r p}"
    unfolding nba_g_E_rtrancl by blast
  lemma nba_g_trancl_path: "(g_E (nba_g A))\<^sup>+ = {(p, target r p) |r p. NBA.path A r p \<and> r \<noteq> []}"
  unfolding nba_g_def graph_rec.simps E_of_succ_def
  proof safe
    show "\<exists> r p. (x, y) = (p, target r p) \<and> NBA.path A r p \<and> r \<noteq> []"
      if "(x, y) \<in> {(p, q). q \<in> successors A p}\<^sup>+" for x y
    using that
    proof induct
      case (base y)
      obtain a where 1: "a \<in> alphabet A" "y \<in> transition A a x" using base by auto
      show ?case
      proof (intro exI conjI)
        show "(x, y) = (x, target [(a, y)] x)" by simp
        show "NBA.path A [(a, y)] x" using 1 by auto
        show "[(a, y)] \<noteq> []" by simp
      qed
    next
      case (step y z)
      obtain r where 1: "y = target r x" "NBA.path A r x" "r \<noteq> []" using step(3) by auto
      obtain a where 2: "a \<in> alphabet A" "z \<in> transition A a y" using step(2) by auto
      show ?case
      proof (intro exI conjI)
        show "(x, z) = (x, target (r @ [(a, z)]) x)" by simp
        show "NBA.path A (r @ [(a, z)]) x" using 1 2 by auto
        show "r @ [(a, z)] \<noteq> []" by simp
      qed
    qed
    show "(p, target r p) \<in> {(u, v). v \<in> successors A u}\<^sup>+" if "NBA.path A r p" "r \<noteq> []" for r p
      using that by (induct) (fastforce intro: trancl_into_trancl2)+
  qed

  lemma nba_g_ipath_run:
    assumes "ipath (g_E (nba_g A)) r"
    obtains w
    where "run A (w ||| smap (r \<circ> Suc) nats) (r 0)"
  proof -
    have 1: "\<exists> a \<in> alphabet A. r (Suc i) \<in> transition A a (r i)" for i
      using assms unfolding ipath_def nba_g_def E_of_succ_def by auto
    obtain wr where 2: "run A wr (r 0)" "\<And> i. target (stake i wr) (r 0) = r i"
    proof (rule nba.invariant_run_index)
      show "\<exists> aq. (fst aq \<in> alphabet A \<and> snd aq \<in> transition A (fst aq) p) \<and> snd aq = r (Suc i) \<and> True"
        if "p = r i" for i p using that 1 by auto
      show "r 0 = r 0" by rule
    qed auto
    have 3: "smap (r \<circ> Suc) nats = smap snd wr"
    proof (rule eqI_snth)
      fix i
      have "smap (r \<circ> Suc) nats !! i = r (Suc i)" by simp
      also have "\<dots> = target (stake (Suc i) wr) (r 0)" unfolding 2(2) by rule
      also have "\<dots> = (r 0 ## trace wr (r 0)) !! Suc i" by simp
      also have "\<dots> = smap snd wr !! i" unfolding nba.trace_alt_def by simp
      finally show "smap (r \<circ> Suc) nats !! i = smap snd wr !! i" by this
    qed
    show ?thesis
    proof
      show "run A (smap fst wr ||| smap (r \<circ> Suc) nats) (r 0)" using 2(1) unfolding 3 by auto
    qed
  qed
  lemma nba_g_run_ipath:
    assumes "run A (w ||| r) p"
    shows "ipath (g_E (nba_g A)) (snth (p ## r))"
  proof
    fix i
    have 1: "w !! i \<in> alphabet A" "r !! i \<in> transition A (w !! i) (target (stake i (w ||| r)) p)"
      using assms by (auto dest: nba.run_snth)
    have 2: "r !! i \<in> successors A ((p ## r) !! i)"
      using 1 unfolding sscan_scons_snth[symmetric] nba.trace_alt_def by auto
    show "((p ## r) !! i, (p ## r) !! Suc i) \<in> g_E (nba_g A)"
      using 2 unfolding nba_g_def graph_rec.simps E_of_succ_def by simp
  qed

  subsection \<open>Indexed Generalized Büchi Graphs\<close>

  definition nba_igbg :: "('label, 'state) nba \<Rightarrow> 'state igb_graph_rec" where
    "nba_igbg A \<equiv> graph_rec.extend (nba_g A)
      \<lparr> igbg_num_acc = 1, igbg_acc = \<lambda> p. if accepting A p then {0} else {} \<rparr>"

  lemma acc_run_language:
    assumes "igb_graph (nba_igbg A)"
    shows "Ex (igb_graph.is_acc_run (nba_igbg A)) \<longleftrightarrow> language A \<noteq> {}"
  proof
    interpret igb_graph "nba_igbg A" using assms by this
    have [simp]: "V0 = g_V0 (nba_g A)" "E = g_E (nba_g A)"
      "num_acc = 1" "0 \<in> acc p \<longleftrightarrow> accepting A p" for p
      unfolding nba_igbg_def graph_rec.defs by simp+
    show "language A \<noteq> {}" if run: "Ex is_acc_run"
    proof -
      obtain r where 1: "is_acc_run r" using run by rule
      have 2: "r 0 \<in> V0" "ipath E r" "is_acc r"
        using 1 unfolding is_acc_run_def graph_defs.is_run_def by auto
      obtain w where 3: "run A (w ||| smap (r \<circ> Suc) nats) (r 0)" using nba_g_ipath_run 2(2) by auto
      have 4: "r 0 ## smap (r \<circ> Suc) nats = smap r nats" by (simp) (metis stream.map_comp smap_siterate)
      have 5: "infs (accepting A) (r 0 ## smap (r \<circ> Suc) nats)"
        using 2(3) unfolding infs_infm is_acc_def 4 by simp
      have "w \<in> language A"
      proof
        show "r 0 \<in> initial A" using nba_g_V0 2(1) by force
        show "run A (w ||| smap (r \<circ> Suc) nats) (r 0)" using 3 by this
        show "infs (accepting A) (r 0 ## smap (r \<circ> Suc) nats)" using 5 by simp
      qed
      then show ?thesis by auto
    qed
    show "Ex is_acc_run" if language: "language A \<noteq> {}"
    proof -
      obtain w where 1: "w \<in> language A" using language by auto
      obtain r p where 2: "p \<in> initial A" "run A (w ||| r) p" "infs (accepting A) (p ## r)" using 1 by rule
      have 3: "infs (accepting A) (p ## r)" using 2(3) by simp
      have "is_acc_run (snth (p ## r))"
      unfolding is_acc_run_def graph_defs.is_run_def
      proof safe
        show "(p ## r) !! 0 \<in> V0" using nba_g_V0 2(1) by force
        show "ipath E (snth (p ## r))" using nba_g_run_ipath 2(2) by force
        show "is_acc (snth (p ## r))" using 3 unfolding infs_infm is_acc_def by simp
      qed
      then show ?thesis by auto
    qed
  qed

end