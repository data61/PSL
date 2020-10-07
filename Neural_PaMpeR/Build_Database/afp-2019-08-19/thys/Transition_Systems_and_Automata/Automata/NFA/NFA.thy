section \<open>Nondeterministic Finite Automata\<close>

theory NFA
imports
  "../../Basic/Sequence_Zip"
  "../../Transition_Systems/Transition_System"
  "../../Transition_Systems/Transition_System_Extra"
  "../../Transition_Systems/Transition_System_Construction"
begin

  record ('label, 'state) nfa =
    succ :: "'label \<Rightarrow> 'state \<Rightarrow> 'state set"
    initial :: "'state set"
    accepting :: "'state set"

  global_interpretation nfa: transition_system_initial
    "\<lambda> a p. snd a" "\<lambda> a p. snd a \<in> succ A (fst a) p" "\<lambda> p. p \<in> initial A"
    for A
    defines path = nfa.path and run = nfa.run and reachable = nfa.reachable and nodes = nfa.nodes
    by this

  abbreviation "target \<equiv> nfa.target"
  abbreviation "states \<equiv> nfa.states"
  abbreviation "trace \<equiv> nfa.trace"

  abbreviation successors :: "('label, 'state, 'more) nfa_scheme \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> nfa.successors TYPE('label) TYPE('more)"

  lemma states_alt_def: "states r p = map snd r" by (induct r arbitrary: p) (auto)
  lemma trace_alt_def: "trace r p = smap snd r" by (coinduction arbitrary: r p) (auto)

  definition language :: "('label, 'state) nfa \<Rightarrow> 'label list set" where
    "language A \<equiv> {map fst r |r p. path A r p \<and> p \<in> initial A \<and> target r p \<in> accepting A}"

  lemma language[intro]:
    assumes "path A (w || r) p" "p \<in> initial A" "target (w || r) p \<in> accepting A" "length w = length r"
    shows "w \<in> language A"
    using assms unfolding language_def by (force iff: split_zip_ex)
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains r p
    where "path A (w || r) p" "p \<in> initial A" "target (w || r) p \<in> accepting A" "length w = length r"
    using assms unfolding language_def by (force iff: split_zip_ex)

  definition product :: "('label, 'state\<^sub>1) nfa \<Rightarrow> ('label, 'state\<^sub>2) nfa \<Rightarrow>
    ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) nfa" where
    "product A B \<equiv>
    \<lparr>
      succ = \<lambda> a (p\<^sub>1, p\<^sub>2). succ A a p\<^sub>1 \<times> succ B a p\<^sub>2,
      initial = initial A \<times> initial B,
      accepting = accepting A \<times> accepting B
    \<rparr>"

  lemma product_simps[simp]:
    "succ (product A B) a (p\<^sub>1, p\<^sub>2) = succ A a p\<^sub>1 \<times> succ B a p\<^sub>2"
    "initial (product A B) = initial A \<times> initial B"
    "accepting (product A B) = accepting A \<times> accepting B"
    unfolding product_def by simp+

  lemma product_target[simp]:
    assumes "length w = length r\<^sub>1" "length r\<^sub>1 = length r\<^sub>2"
    shows "target (w || r\<^sub>1 || r\<^sub>2) (p\<^sub>1, p\<^sub>2) = (target (w || r\<^sub>1) p\<^sub>1, target (w || r\<^sub>2) p\<^sub>2)"
    using assms by (induct arbitrary: p\<^sub>1 p\<^sub>2 rule: list_induct3) (auto)
  lemma product_path[iff]:
    assumes "length w = length r\<^sub>1" "length r\<^sub>1 = length r\<^sub>2"
    shows "path (product A B) (w || r\<^sub>1 || r\<^sub>2) (p\<^sub>1, p\<^sub>2) \<longleftrightarrow> path A (w || r\<^sub>1) p\<^sub>1 \<and> path B (w || r\<^sub>2) p\<^sub>2"
    using assms by (induct arbitrary: p\<^sub>1 p\<^sub>2 rule: list_induct3) (auto)

  lemma product_language[simp]: "language (product A B) = language A \<inter> language B"
    by (fastforce iff: split_zip)

end
