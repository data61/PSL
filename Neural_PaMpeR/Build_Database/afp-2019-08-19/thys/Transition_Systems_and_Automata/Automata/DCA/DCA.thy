section \<open>Deterministic Co-Büchi Automata\<close>

theory DCA
imports
  "../../Basic/Sequence_Zip"
  "../../Basic/Acceptance"
  "../../Transition_Systems/Transition_System"
  "../../Transition_Systems/Transition_System_Extra"
  "../../Transition_Systems/Transition_System_Construction"
begin

  datatype ('label, 'state) dca = dca
    (alphabet: "'label set")
    (initial: "'state")
    (succ: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (rejecting: "'state \<Rightarrow> bool")

  global_interpretation dca: transition_system_initial
    "succ A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A"
    for A
    defines path = dca.path and run = dca.run and reachable = dca.reachable and nodes = dca.nodes and
      enableds = dca.enableds and paths = dca.paths and runs = dca.runs
    by this

  abbreviation target where "target \<equiv> dca.target"
  abbreviation states where "states \<equiv> dca.states"
  abbreviation trace where "trace \<equiv> dca.trace"

  abbreviation successors :: "('label, 'state) dca \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> dca.successors TYPE('label)"

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
      using that by (coinduction arbitrary: w p) (force elim: dca.run.cases)
    show "run A w p" if "w \<in> streams (alphabet A)"
      using that by (coinduction arbitrary: w p) (force elim: streams.cases)
  qed

  definition language :: "('label, 'state) dca \<Rightarrow> 'label stream set" where
    "language A \<equiv> {w. run A w (initial A) \<and> \<not> infs (rejecting A) (trace A w (initial A))}"

  lemma language[intro]:
    assumes "run A w (initial A)" "\<not> infs (rejecting A) (trace A w (initial A))"
    shows "w \<in> language A"
    using assms unfolding language_def by auto
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains "run A w (initial A)" "\<not> infs (rejecting A) (trace A w (initial A))"
    using assms unfolding language_def by auto

  lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
    unfolding language_def run_alt_def using sset_streams by auto

end