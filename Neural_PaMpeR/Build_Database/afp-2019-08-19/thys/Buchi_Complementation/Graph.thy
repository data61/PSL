section \<open>Run Graphs\<close>

theory Graph
imports "Transition_Systems_and_Automata.NBA"
begin

  type_synonym 'state node = "nat \<times> 'state"

  abbreviation "ginitial A \<equiv> {0} \<times> initial A"
  abbreviation "gaccepting A \<equiv> accepting A \<circ> snd"

  global_interpretation graph: transition_system_initial
    "const"
    "\<lambda> u (k, p). w !! k \<in> alphabet A \<and> u \<in> {Suc k} \<times> succ A (w !! k) p \<inter> V"
    "\<lambda> v. v \<in> ginitial A \<inter> V"
    for A w V
    defines
      gpath = graph.path and grun = graph.run and
      greachable = graph.reachable and gnodes = graph.nodes
    by this

  text \<open>We disable rules that are degenerate due to @{term "execute = const"}.\<close>
  declare graph.reachable.execute[rule del]
  declare graph.nodes.execute[rule del]

  abbreviation "gtarget \<equiv> graph.target"
  abbreviation "gstates \<equiv> graph.states"
  abbreviation "gtrace \<equiv> graph.trace"

  abbreviation gsuccessors :: "('label, 'state) nba \<Rightarrow> 'label stream \<Rightarrow>
    'state node set \<Rightarrow> 'state node \<Rightarrow> 'state node set" where
    "gsuccessors A w V \<equiv> graph.successors TYPE('label) w A V"

  abbreviation "gusuccessors A w \<equiv> gsuccessors A w UNIV"
  abbreviation "gupath A w \<equiv> gpath A w UNIV"
  abbreviation "gurun A w \<equiv> grun A w UNIV"
  abbreviation "gureachable A w \<equiv> greachable A w UNIV"
  abbreviation "gunodes A w \<equiv> gnodes A w UNIV"

  lemma gtarget_alt_def: "gtarget r v = last (v # r)" using fold_const by this
  lemma gstates_alt_def: "gstates r v = r" by simp
  lemma gtrace_alt_def: "gtrace r v = r" by simp

  lemma gpath_elim[elim?]:
    assumes "gpath A w V s v"
    obtains r k p
    where "s = [Suc k ..< Suc k + length r] || r" "v = (k, p)"
  proof -
    obtain t r where 1: "s = t || r" "length t = length r"
      using zip_map_fst_snd[of s] by (metis length_map)
    obtain k p where 2: "v = (k, p)" by force
    have 3: "t = [Suc k ..< Suc k + length r]"
    using assms 1 2
    proof (induct arbitrary: t r k p)
      case (nil v)
      then show ?case by (metis add_0_right le_add1 length_0_conv length_zip min.idem upt_conv_Nil)
    next
      case (cons u v s)
      have 1: "t || r = (hd t, hd r) # (tl t || tl r)"
        by (metis cons.prems(1) hd_Cons_tl neq_Nil_conv zip.simps(1) zip_Cons_Cons zip_Nil)
      have 2: "s = tl t || tl r" using cons 1 by simp
      have "t = hd t # tl t" using cons(4) by (metis hd_Cons_tl list.simps(3) zip_Nil)
      also have "hd t = Suc k" using "1" cons.hyps(1) cons.prems(1) cons.prems(3) by auto
      also have "tl t = [Suc (Suc k) ..< Suc (Suc k) + length (tl r)]"
        using cons(3)[OF 2] using "1" \<open>hd t = Suc k\<close> cons.prems(1) cons.prems(2) by auto
      finally show ?case using cons.prems(2) upt_rec by auto
    qed
    show ?thesis using that 1 2 3 by simp
  qed

  lemma gpath_path[symmetric]: "path A (stake (length r) (sdrop k w) || r) p \<longleftrightarrow>
    gpath A w UNIV ([Suc k ..< Suc k + length r] || r) (k, p)"
  proof (induct r arbitrary: k p)
    case (Nil)
    show ?case by auto
  next
    case (Cons q r)
    have 1: "path A (stake (length r) (sdrop (Suc k) w) || r) q \<longleftrightarrow>
      gpath A w UNIV ([Suc (Suc k) ..< Suc k + length (q # r)] || r) (Suc k, q)"
      using Cons[of "Suc k" "q"] by simp
    have "stake (length (q # r)) (sdrop k w) || q # r =
      (w !! k, q) # (stake (length r) (sdrop (Suc k) w) || r)" by simp
    also have "path A \<dots> p \<longleftrightarrow>
      gpath A w UNIV ((Suc k, q) # ([Suc (Suc k) ..< Suc k + length (q # r)] || r)) (k, p)"
      using 1 by auto
    also have "(Suc k, q) # ([Suc (Suc k) ..< Suc k + length (q # r)] || r) =
      Suc k # [Suc (Suc k) ..< Suc k + length (q # r)] || q # r" unfolding zip_Cons_Cons by rule
    also have "Suc k # [Suc (Suc k) ..< Suc k + length (q # r)] = [Suc k ..< Suc k + length (q # r)]"
      by (simp add: upt_rec)
    finally show ?case by this
  qed

  lemma grun_elim[elim?]:
    assumes "grun A w V s v"
    obtains r k p
    where "s = fromN (Suc k) ||| r" "v = (k, p)"
  proof -
    obtain t r where 1: "s = t ||| r" using szip_smap by metis
    obtain k p where 2: "v = (k, p)" by force
    have 3: "t = fromN (Suc k)"
      using assms unfolding 1 2
      by (coinduction arbitrary: t r k p) (force iff: eq_scons elim: graph.run.cases)
    show ?thesis using that 1 2 3 by simp
  qed

  lemma run_grun:
    assumes "run A (sdrop k w ||| r) p"
    shows "gurun A w (fromN (Suc k) ||| r) (k, p)"
    using assms by (coinduction arbitrary: k p r) (auto elim: nba.run.cases)

  lemma grun_run:
    assumes "grun A w V (fromN (Suc k) ||| r) (k, p)"
    shows "run A (sdrop k w ||| r) p"
  proof -
    have 2: "\<exists> ka wa. sdrop k (stl w :: 'a stream) = sdrop ka wa \<and> P ka wa" if "P (Suc k) w" for P k w
      using that by (metis sdrop.simps(2))
    show ?thesis using assms by (coinduction arbitrary: k p w r) (auto intro!: 2 elim: graph.run.cases)
  qed

  lemma greachable_reachable:
    fixes l q k p
    defines "u \<equiv> (l, q)"
    defines "v \<equiv> (k, p)"
    assumes "u \<in> greachable A w V v"
    shows "q \<in> reachable A p"
  using assms(3, 1, 2)
  proof (induct arbitrary: l q k p)
    case reflexive
    then show ?case by auto
  next
    case (execute u)
    have 1: "q \<in> successors A (snd u)" using execute by auto
    have "snd u \<in> reachable A p" using execute by auto
    also have "q \<in> reachable A (snd u)" using 1 by blast
    finally show ?case by this
  qed

  lemma gnodes_nodes: "gnodes A w V \<subseteq> UNIV \<times> nodes A"
  proof
    fix v
    assume "v \<in> gnodes A w V"
    then show "v \<in> UNIV \<times> nodes A" by induct auto
  qed

  lemma gpath_subset:
    assumes "gpath A w V r v"
    assumes "set (gstates r v) \<subseteq> U"
    shows "gpath A w U r v"
    using assms by induct auto
  lemma grun_subset:
    assumes "grun A w V r v"
    assumes "sset (gtrace r v) \<subseteq> U"
    shows "grun A w U r v"
  using assms
  proof (coinduction arbitrary: r v)
    case (run a s r v)
    have 1: "grun A w V s a" using run(1, 2) by fastforce
    have 2: "a \<in> gusuccessors A w v" using run(1, 2) by fastforce
    show ?case using 1 2 run(1, 3) by force
  qed

  lemma greachable_subset: "greachable A w V v \<subseteq> insert v V"
  proof
    fix u
    assume "u \<in> greachable A w V v"
    then show "u \<in> insert v V" by induct auto
  qed

  lemma gtrace_infinite:
    assumes "grun A w V r v"
    shows "infinite (sset (gtrace r v))"
    using assms by (metis grun_elim gtrace_alt_def infinite_Ici sset_fromN sset_szip_finite)

  lemma infinite_greachable_gtrace:
    assumes "grun A w V r v"
    assumes "u \<in> sset (gtrace r v)"
    shows "infinite (greachable A w V u)"
  proof -
    obtain i where 1: "u = gtrace r v !! i" using sset_range imageE assms(2) by metis
    have 2: "gtarget (stake (Suc i) r) v = u" unfolding 1 sscan_snth by rule
    have "infinite (sset (sdrop (Suc i) (gtrace r v)))"
      using gtrace_infinite[OF assms(1)]
      by (metis List.finite_set finite_Un sset_shift stake_sdrop)
    also have "sdrop (Suc i) (gtrace r v) = gtrace (sdrop (Suc i) r) (gtarget (stake (Suc i) r) v)"
      by simp
    also have "sset \<dots> \<subseteq> greachable A w V u"
      using assms(1) 2 by (metis graph.reachable.reflexive graph.reachable_trace graph.run_sdrop)
    finally show ?thesis by this
  qed

  lemma finite_nodes_gsuccessors:
    assumes "finite (nodes A)"
    assumes "v \<in> gunodes A w"
    shows "finite (gusuccessors A w v)"
  proof -
    have "gusuccessors A w v \<subseteq> gureachable A w v" by rule
    also have "\<dots> \<subseteq> gunodes A w" using assms(2) by blast
    also have "\<dots> \<subseteq> UNIV \<times> nodes A" using gnodes_nodes by this
    finally have 3: "gusuccessors A w v \<subseteq> UNIV \<times> nodes A" by this
    have "gusuccessors A w v \<subseteq> {Suc (fst v)} \<times> nodes A" using 3 by auto
    also have "finite \<dots>" using assms(1) by simp
    finally show ?thesis by this
  qed

end
