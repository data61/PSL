section \<open>Nondeterministic Büchi Automata\<close>

theory NBA
imports
  "../../Basic/Sequence_Zip"
  "../../Basic/Acceptance"
  "../../Transition_Systems/Transition_System"
  "../../Transition_Systems/Transition_System_Extra"
  "../../Transition_Systems/Transition_System_Construction"
begin

  datatype ('label, 'state) nba = nba
    (alphabet: "'label set")
    (initial: "'state set")
    (succ: "'label \<Rightarrow> 'state \<Rightarrow> 'state set")
    (accepting: "'state pred")

  global_interpretation nba: transition_system_initial
    "\<lambda> a p. snd a" "\<lambda> a p. fst a \<in> alphabet A \<and> snd a \<in> succ A (fst a) p" "\<lambda> p. p \<in> initial A"
    for A
    defines path = nba.path and run = nba.run and reachable = nba.reachable and nodes = nba.nodes and
      enableds = nba.enableds and paths = nba.paths and runs = nba.runs
    by this

  abbreviation "target \<equiv> nba.target"
  abbreviation "states \<equiv> nba.states"
  abbreviation "trace \<equiv> nba.trace"

  lemma states_alt_def: "states r p = map snd r" by (induct r arbitrary: p) (auto)
  lemma trace_alt_def: "trace r p = smap snd r" by (coinduction arbitrary: r p) (auto)

  abbreviation successors :: "('label, 'state) nba \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> nba.successors TYPE('label)"

  lemma successors_alt_def: "successors A p = (\<Union> a \<in> alphabet A. succ A a p)" by auto

  lemma reachable_succ[intro]:
    assumes "a \<in> alphabet A" "q \<in> reachable A p" "r \<in> succ A a q"
    shows "r \<in> reachable A p"
    using nba.reachable.execute assms by force
  lemma nodes_succ[intro]:
    assumes "a \<in> alphabet A" "p \<in> nodes A" "q \<in> succ A a p"
    shows "q \<in> nodes A"
    using nba.nodes.execute assms by force

  definition language :: "('label, 'state) nba \<Rightarrow> 'label stream set" where
    "language A \<equiv> {w |w r p. p \<in> initial A \<and> run A (w ||| r) p \<and> infs (accepting A) (trace (w ||| r) p)}"

  lemma language[intro]:
    assumes "p \<in> initial A" "run A (w ||| r) p" "infs (accepting A) (trace (w ||| r) p)"
    shows "w \<in> language A"
    using assms unfolding language_def by auto
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains r p
    where "p \<in> initial A" "run A (w ||| r) p" "infs (accepting A) (trace (w ||| r) p)"
    using assms unfolding language_def by auto

  lemma run_alphabet:
    assumes "run A (w ||| r) p"
    shows "w \<in> streams (alphabet A)"
    using assms by (coinduction arbitrary: w r p) (metis nba.run.cases stream.map szip_smap szip_smap_fst)
  lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
    unfolding language_def by (auto dest: run_alphabet)

  instantiation nba :: (type, type) order
  begin

    definition less_eq_nba :: "('a, 'b) nba \<Rightarrow> ('a, 'b) nba \<Rightarrow> bool" where
      "A \<le> B \<equiv> alphabet A \<le> alphabet B \<and> initial A \<le> initial B \<and>
        succ A \<le> succ B \<and> accepting A \<le> accepting B"
    definition less_nba :: "('a, 'b) nba \<Rightarrow> ('a, 'b) nba \<Rightarrow> bool" where
      "less_nba A B \<equiv> A \<le> B \<and> A \<noteq> B"

    instance by (intro_classes) (auto simp: less_eq_nba_def less_nba_def nba.expand)

  end

  lemma nodes_mono: "mono nodes"
  proof
    fix A B :: "('label, 'state) nba"
    assume 1: "A \<le> B"
    have 2: "alphabet A \<subseteq> alphabet B" using 1 unfolding less_eq_nba_def by auto
    have 3: "initial A \<subseteq> initial B" using 1 unfolding less_eq_nba_def by auto
    have 4: "succ A a p \<subseteq> succ B a p" for a p using 1 unfolding less_eq_nba_def le_fun_def by auto
    have 5: "p \<in> nodes B" if "p \<in> nodes A" for p using that 2 3 4 by induct fastforce+
    show "nodes A \<subseteq> nodes B" using 5 by auto
  qed

  lemma language_mono: "mono language"
  proof
    fix A B :: "('label, 'state) nba"
    assume 1: "A \<le> B"
    have 2: "alphabet A \<subseteq> alphabet B" using 1 unfolding less_eq_nba_def by auto
    have 3: "initial A \<subseteq> initial B" using 1 unfolding less_eq_nba_def by auto
    have 4: "succ A a p \<subseteq> succ B a p" for a p using 1 unfolding less_eq_nba_def le_fun_def by auto
    have 5: "accepting A p \<Longrightarrow> accepting B p" for p using 1 unfolding less_eq_nba_def by auto
    have 6: "run B wr p" if "run A wr p" for wr p using that 2 4 by coinduct auto
    have 7: "infs (accepting B) w" if "infs (accepting A) w" for w using infs_mono that 5 by metis
    show "language A \<subseteq> language B" using 3 6 7 by blast
  qed

  lemma simulation_language:
    assumes "alphabet A \<subseteq> alphabet B"
    assumes "\<And> p. p \<in> initial A \<Longrightarrow> \<exists> q \<in> initial B. (p, q) \<in> R"
    assumes "\<And> a p p' q. p' \<in> succ A a p \<Longrightarrow> (p, q) \<in> R \<Longrightarrow> \<exists> q' \<in> succ B a q. (p', q') \<in> R"
    assumes "\<And> p q. (p, q) \<in> R \<Longrightarrow> accepting A p \<Longrightarrow> accepting B q"
    shows "language A \<subseteq> language B"
  proof
    fix w
    assume 1: "w \<in> language A"
    obtain r p where 2: "p \<in> initial A" "run A (w ||| r) p" "infs (accepting A) (trace (w ||| r) p)"
      using 1 by rule
    define P where "P n q \<equiv> (target (stake n (w ||| r)) p, q) \<in> R" for n q
    obtain q where 3: "q \<in> initial B" "(p, q) \<in> R" using assms(2) 2(1) by auto
    obtain ws where 4:
      "run B ws q" "\<And> i. P (0 + i) (target (stake i ws) q)" "\<And> i. fst (ws !! i) = w !! (0 + i)"
    proof (rule nba.invariant_run_index)
      have "stake k (w ||| r) @- (w !! k, target (stake (Suc k) (w ||| r)) p) ##
        sdrop (Suc k) (w ||| r) = w ||| r" for k
        by (metis id_stake_snth_sdrop snth_szip sscan_snth szip_smap_snd trace_alt_def)
      also have "run A \<dots> p" using 2(2) by this
      finally show "\<exists> a. (fst a \<in> alphabet B \<and> snd a \<in> succ B (fst a) q) \<and>
        P (Suc n) (snd a) \<and> fst a = w !! n" if "P n q" for n q
        using assms(1, 3) that unfolding P_def by fastforce
      show "P 0 q" unfolding P_def using 3(2) by auto
    qed rule
    obtain s where 5: "ws = w ||| s" using 4(3) by (metis add.left_neutral eqI_snth snth_smap szip_smap)
    show "w \<in> language B"
    proof
      show "q \<in> initial B" using 3(1) by this
      show "run B (w ||| s) q" using 4(1) unfolding 5 by this
      have 6: "(\<lambda> a b. (a, b) \<in> R) \<le> (\<lambda> a b. accepting A a \<longrightarrow> accepting B b)" using assms(4) by auto
      have 7: "stream_all2 (\<lambda> p q. (p, q) \<in> R) (trace (w ||| r) p) (trace (w ||| s) q)"
        using 4(2) unfolding P_def 5 by (simp add: stream_rel_snth del: stake.simps(2))
      have 8: "stream_all2 (\<lambda> a b. accepting A a \<longrightarrow> accepting B b)
        (trace (w ||| r) p) (trace (w ||| s) q)" using stream.rel_mono 6 7 by auto
      show "infs (accepting B) (trace (w ||| s) q)" using infs_mono_strong 8 2(3) by this
    qed
  qed

end