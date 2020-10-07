section \<open>Deterministic Finite Automata\<close>

theory DFA
imports
  "../../Transition_Systems/Transition_System"
  "../../Transition_Systems/Transition_System_Extra"
  "../../Transition_Systems/Transition_System_Construction"
begin

  record ('label, 'state) dfa =
    succ :: "'label \<Rightarrow> 'state \<Rightarrow> 'state"
    initial :: "'state"
    accepting :: "'state set"

  global_interpretation dfa: transition_system_initial "succ A" "top" "\<lambda> p. p = initial A"
    for A
    defines path = dfa.path and run = dfa.run and reachable = dfa.reachable and nodes = dfa.nodes
    by this

  abbreviation target :: "('label, 'state, 'more) dfa_scheme \<Rightarrow> 'label list \<Rightarrow> 'state \<Rightarrow> 'state" where
    "target \<equiv> dfa.target TYPE('more)"
  abbreviation states :: "('label, 'state, 'more) dfa_scheme \<Rightarrow> 'label list \<Rightarrow> 'state \<Rightarrow> 'state list" where
    "states \<equiv> dfa.states TYPE('more)"
  abbreviation trace :: "('label, 'state, 'more) dfa_scheme \<Rightarrow> 'label stream \<Rightarrow> 'state \<Rightarrow> 'state stream" where
    "trace \<equiv> dfa.trace TYPE('more)"

  abbreviation successors :: "('label, 'state, 'more) dfa_scheme \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> dfa.successors TYPE('label) TYPE('more)"

  definition language :: "('label, 'state) dfa \<Rightarrow> 'label list set" where
    "language A \<equiv> {w. target A w (initial A) \<in> accepting A}"

  lemma language[intro]:
    assumes "target A w (initial A) \<in> accepting A"
    shows "w \<in> language A"
    using assms unfolding language_def by auto
  lemma language_elim[elim]:
    assumes "w \<in> language A"
    obtains "target A w (initial A) \<in> accepting A"
    using assms unfolding language_def by auto

  definition complement :: "('label, 'state) dfa \<Rightarrow> ('label, 'state) dfa" where
    "complement A \<equiv> \<lparr> succ = succ A, initial = initial A, accepting = - accepting A \<rparr>"

  lemma complement_simps[simp]:
    "succ (complement A) = succ A"
    "initial (complement A) = initial A"
    "accepting (complement A) = - accepting A"
    unfolding complement_def by simp+

  lemma complement_language[simp]: "language (complement A) = - language A" by force

  definition product :: "('label, 'state\<^sub>1) dfa \<Rightarrow> ('label, 'state\<^sub>2) dfa \<Rightarrow>
    ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) dfa" where
    "product A B \<equiv>
    \<lparr>
      succ = \<lambda> a (p\<^sub>1, p\<^sub>2). (succ A a p\<^sub>1, succ B a p\<^sub>2),
      initial = (initial A, initial B),
      accepting = accepting A \<times> accepting B
    \<rparr>"

  lemma product_simps[simp]:
    "succ (product A B) a (p\<^sub>1, p\<^sub>2) = (succ A a p\<^sub>1, succ B a p\<^sub>2)"
    "initial (product A B) = (initial A, initial B)"
    "accepting (product A B) = accepting A \<times> accepting B"
    unfolding product_def by simp+

  lemma product_target[simp]: "target (product A B) r (p\<^sub>1, p\<^sub>2) = (target A r p\<^sub>1, target B r p\<^sub>2)"
    by (induct r arbitrary: p\<^sub>1 p\<^sub>2) (auto)

  lemma product_language[simp]: "language (product A B) = language A \<inter> language B" by force

end
