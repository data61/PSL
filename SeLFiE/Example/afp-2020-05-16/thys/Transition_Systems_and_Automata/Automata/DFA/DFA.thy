section \<open>Deterministic Finite Automata\<close>

theory DFA
imports "../Deterministic"
begin

  datatype ('label, 'state) dfa = dfa
    (alphabet: "'label set")
    (initial: "'state")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (accepting: "'state pred")

  global_interpretation dfa: automaton dfa alphabet initial transition accepting
    defines path = dfa.path and run = dfa.run and reachable = dfa.reachable and nodes = dfa.nodes
    by unfold_locales auto
  global_interpretation dfa: automaton_path dfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    defines language = dfa.language
    by standard

  abbreviation target where "target \<equiv> dfa.target"
  abbreviation states where "states \<equiv> dfa.states"
  abbreviation trace where "trace \<equiv> dfa.trace"
  abbreviation successors where "successors \<equiv> dfa.successors TYPE('label)"

  global_interpretation intersection: automaton_intersection_path
    dfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    dfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    dfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    "\<lambda> c\<^sub>1 c\<^sub>2 (p, q). c\<^sub>1 p \<and> c\<^sub>2 q"
    defines intersect = intersection.product
    by (unfold_locales) (auto simp: zip_eq_Nil_iff)

  global_interpretation union: automaton_union_path
    dfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    dfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    dfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    "\<lambda> c\<^sub>1 c\<^sub>2 (p, q). c\<^sub>1 p \<or> c\<^sub>2 q"
    defines union = union.product
    by (unfold_locales) (auto simp: zip_eq_Nil_iff)

  global_interpretation complement: automaton_complement_path
    dfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    dfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    "\<lambda> c p. \<not> c p"
    defines complement = complement.complement
    by unfold_locales auto

end