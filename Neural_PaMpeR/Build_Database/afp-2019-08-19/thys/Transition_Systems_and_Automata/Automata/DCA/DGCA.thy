section \<open>Deterministic Co-Generalized Co-Büchi Automata\<close>

theory DGCA
imports
  "DCA"
  "../../Transition_Systems/Transition_System_Degeneralization"
begin

  datatype ('label, 'state) dgca = dgca
    (alphabet: "'label set")
    (initial: "'state")
    (succ: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (rejecting: "'state pred gen")

  global_interpretation dgca: transition_system_initial_generalized
    "succ A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A" "rejecting A"
    for A
    defines path = dgca.path and run = dgca.run and reachable = dgca.reachable and nodes = dgca.nodes and
      enableds = dgca.enableds and paths = dgca.paths and runs = dgca.runs and
      dexecute = dgca.dexecute and denabled = dgca.denabled and dinitial = dgca.dinitial and
      drejecting = dgca.dcondition
    by this

  abbreviation target where "target \<equiv> dgca.target"
  abbreviation states where "states \<equiv> dgca.states"
  abbreviation trace where "trace \<equiv> dgca.trace"

  abbreviation successors :: "('label, 'state) dgca \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> dgca.successors TYPE('label)"

  lemma path_alt_def: "path A w p \<longleftrightarrow> set w \<subseteq> alphabet A"
  unfolding lists_iff_set[symmetric]
  proof
    show "w \<in> lists (alphabet A)" if "path A w p" using that by (induct arbitrary: p) (auto)
    show "path A w p" if "w \<in> lists (alphabet A)" using that by (induct arbitrary: p) (auto)
  qed
  lemma run_alt_def: "run A w p \<longleftrightarrow> sset w \<subseteq> alphabet A"
  unfolding streams_iff_sset[symmetric]
  proof
    show "w \<in> streams (alphabet A)" if "run A w p"
      using that by (coinduction arbitrary: w p) (force elim: dgca.run.cases)
    show "run A w p" if "w \<in> streams (alphabet A)"
      using that by (coinduction arbitrary: w p) (force elim: streams.cases)
  qed

  definition language :: "('label, 'state) dgca \<Rightarrow> 'label stream set" where
    "language A \<equiv> {w. run A w (initial A) \<and> cogen fins (rejecting A) (trace A w (initial A))}"

  lemma language[intro]:
    assumes "run A w (initial A)" "cogen fins (rejecting A) (trace A w (initial A))"
    shows "w \<in> language A"
    using assms unfolding language_def by auto
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains "run A w (initial A)" "cogen fins (rejecting A) (trace A w (initial A))"
    using assms unfolding language_def by auto

  lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
    unfolding language_def run_alt_def using sset_streams by auto

  definition degen :: "('label, 'state) dgca \<Rightarrow> ('label, 'state degen) dca" where
    "degen A \<equiv> dca (alphabet A) (The (dinitial A)) (dexecute A) (drejecting A)"

  lemma degen_simps[simp]:
    "dca.alphabet (degen A) = alphabet A"
    "dca.initial (degen A) = (initial A, 0)"
    "dca.succ (degen A) = dexecute A"
    "dca.rejecting (degen A) = drejecting A"
    unfolding degen_def dgca.dinitial_def by auto

  lemma degen_trace[simp]: "dca.trace (degen A) = dgca.degen.trace A" unfolding degen_simps by rule
  lemma degen_run[simp]: "dca.run (degen A) = dgca.degen.run A"
    unfolding DCA.run_def degen_simps dgca.denabled_def case_prod_beta' by rule
  lemma degen_nodes[simp]: "DCA.nodes (degen A) = dgca.degen.nodes TYPE('label) A"
    unfolding DCA.nodes_def degen_simps
    unfolding dgca.denabled_def dgca.dinitial_def
    unfolding prod_eq_iff case_prod_beta' prod.sel
    by rule

  lemma degen_nodes_finite[iff]: "finite (DCA.nodes (degen A)) \<longleftrightarrow> finite (DGCA.nodes A)" by simp
  lemma degen_nodes_card: "card (DCA.nodes (degen A)) \<le> max 1 (length (rejecting A)) * card (DGCA.nodes A)"
    using dgca.degen_nodes_card by simp

  lemma degen_language[simp]: "DCA.language (degen A) = DGCA.language A"
    unfolding DCA.language_def DGCA.language_def degen_simps
    unfolding degen_trace degen_run
    unfolding dgca.degen_run dgca.degen_infs cogen_def
    unfolding ball_simps(10)
    by rule

end