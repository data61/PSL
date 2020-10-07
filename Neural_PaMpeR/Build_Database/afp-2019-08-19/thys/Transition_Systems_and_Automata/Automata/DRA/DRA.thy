section \<open>Deterministic Rabin Automata\<close>

theory DRA
imports
  "../../Basic/Sequence_Zip"
  "../../Basic/Acceptance"
  "../../Transition_Systems/Transition_System"
  "../../Transition_Systems/Transition_System_Extra"
  "../../Transition_Systems/Transition_System_Construction"
begin

  datatype ('label, 'state) dra = dra
    (alphabet: "'label set")
    (initial: "'state")
    (succ: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (accepting: "'state rabin gen")

  global_interpretation dra: transition_system_initial
    "succ A" "\<lambda> a p. a \<in> alphabet A" "\<lambda> p. p = initial A"
    for A
    defines path = dra.path and run = dra.run and reachable = dra.reachable and nodes = dra.nodes and
      enableds = dra.enableds and paths = dra.paths and runs = dra.runs
    by this

  abbreviation target where "target \<equiv> dra.target"
  abbreviation states where "states \<equiv> dra.states"
  abbreviation trace where "trace \<equiv> dra.trace"

  abbreviation successors :: "('label, 'state) dra \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> dra.successors TYPE('label)"

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
      using that by (coinduction arbitrary: w p) (force elim: dra.run.cases)
    show "run A w p" if "w \<in> streams (alphabet A)"
      using that by (coinduction arbitrary: w p) (force elim: streams.cases)
  qed

  definition language :: "('label, 'state) dra \<Rightarrow> 'label stream set" where
    "language A \<equiv> {w. run A w (initial A) \<and> cogen rabin (accepting A) (trace A w (initial A))}"

  lemma language[intro]:
    assumes "run A w (initial A)" "cogen rabin (accepting A) (trace A w (initial A))"
    shows "w \<in> language A"
    using assms unfolding language_def by auto
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains "run A w (initial A)" "cogen rabin (accepting A) (trace A w (initial A))"
    using assms unfolding language_def by auto

  lemma language_alphabet: "language A \<subseteq> streams (alphabet A)"
    unfolding language_def run_alt_def using sset_streams by auto

end