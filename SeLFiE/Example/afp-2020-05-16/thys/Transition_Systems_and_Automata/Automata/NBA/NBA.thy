section \<open>Nondeterministic Büchi Automata\<close>

theory NBA
imports "../Nondeterministic"
begin

  datatype ('label, 'state) nba = nba
    (alphabet: "'label set")
    (initial: "'state set")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state set")
    (accepting: "'state pred")

  global_interpretation nba: automaton nba alphabet initial transition accepting
    defines path = nba.path and run = nba.run and reachable = nba.reachable and nodes = nba.nodes
    by unfold_locales auto
  global_interpretation nba: automaton_run nba alphabet initial transition accepting "\<lambda> P w r p. infs P (p ## r)"
    defines language = nba.language
    by standard

  abbreviation target where "target \<equiv> nba.target"
  abbreviation states where "states \<equiv> nba.states"
  abbreviation trace where "trace \<equiv> nba.trace"
  abbreviation successors where "successors \<equiv> nba.successors TYPE('label)"

  instantiation nba :: (type, type) order
  begin

    definition less_eq_nba :: "('a, 'b) nba \<Rightarrow> ('a, 'b) nba \<Rightarrow> bool" where
      "A \<le> B \<equiv> alphabet A \<le> alphabet B \<and> initial A \<le> initial B \<and>
        transition A \<le> transition B \<and> accepting A \<le> accepting B"
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
    have 4: "transition A a p \<subseteq> transition B a p" for a p using 1 unfolding less_eq_nba_def le_fun_def by auto
    have 5: "p \<in> nodes B" if "p \<in> nodes A" for p using that 2 3 4 by induct fastforce+
    show "nodes A \<subseteq> nodes B" using 5 by auto
  qed

  lemma language_mono: "mono language"
  proof
    fix A B :: "('label, 'state) nba"
    assume 1: "A \<le> B"
    have 2: "alphabet A \<subseteq> alphabet B" using 1 unfolding less_eq_nba_def by auto
    have 3: "initial A \<subseteq> initial B" using 1 unfolding less_eq_nba_def by auto
    have 4: "transition A a p \<subseteq> transition B a p" for a p using 1 unfolding less_eq_nba_def le_fun_def by auto
    have 5: "accepting A p \<Longrightarrow> accepting B p" for p using 1 unfolding less_eq_nba_def by auto
    have 6: "run B wr p" if "run A wr p" for wr p using that 2 4 by coinduct auto
    have 7: "infs (accepting B) w" if "infs (accepting A) w" for w using infs_mono that 5 by metis
    show "language A \<subseteq> language B" using 3 6 7 by blast
  qed

  lemma simulation_language:
    assumes "alphabet A \<subseteq> alphabet B"
    assumes "\<And> p. p \<in> initial A \<Longrightarrow> \<exists> q \<in> initial B. (p, q) \<in> R"
    assumes "\<And> a p p' q. p' \<in> transition A a p \<Longrightarrow> (p, q) \<in> R \<Longrightarrow> \<exists> q' \<in> transition B a q. (p', q') \<in> R"
    assumes "\<And> p q. (p, q) \<in> R \<Longrightarrow> accepting A p \<Longrightarrow> accepting B q"
    shows "language A \<subseteq> language B"
  proof
    fix w
    assume 1: "w \<in> language A"
    obtain r p where 2: "p \<in> initial A" "run A (w ||| r) p" "infs (accepting A) (p ## r)" using 1 by rule
    define P where "P n q \<equiv> (target (stake n (w ||| r)) p, q) \<in> R" for n q
    obtain q where 3: "q \<in> initial B" "(p, q) \<in> R" using assms(2) 2(1) by auto
    obtain ws where 4:
      "run B ws q" "\<And> i. P (0 + i) (target (stake i ws) q)" "\<And> i. fst (ws !! i) = w !! (0 + i)"
    proof (rule nba.invariant_run_index)
      have "stake k (w ||| r) @- (w !! k, target (stake (Suc k) (w ||| r)) p) ##
        sdrop (Suc k) (w ||| r) = w ||| r" for k
        by (metis id_stake_snth_sdrop snth_szip sscan_snth szip_smap_snd nba.trace_alt_def)
      also have "run A \<dots> p" using 2(2) by this
      finally show "\<exists> a. (fst a \<in> alphabet B \<and> snd a \<in> transition B (fst a) q) \<and>
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
      have 8: "stream_all2 (\<lambda> a b. accepting A a \<longrightarrow> accepting B b) r s"
        using stream.rel_mono 6 7 unfolding nba.trace_alt_def by auto
      show "infs (accepting B) (q ## s)" using infs_mono_strong 8 2(3) by simp
    qed
  qed

end