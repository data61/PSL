section \<open>Nondeterministic Finite Automata\<close>

theory NFA
imports "../Nondeterministic"
begin

  datatype ('label, 'state) nfa = nfa
    (alphabet: "'label set")
    (initial: "'state set")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state set")
    (accepting: "'state pred")

  global_interpretation nfa: automaton nfa alphabet initial transition accepting
    defines path = nfa.path and run = nfa.run and reachable = nfa.reachable and nodes = nfa.nodes
    by unfold_locales auto
  global_interpretation nfa: automaton_path nfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    defines language = nfa.language
    by standard

  abbreviation target where "target \<equiv> nfa.target"
  abbreviation states where "states \<equiv> nfa.states"
  abbreviation trace where "trace \<equiv> nfa.trace"
  abbreviation successors where "successors \<equiv> nfa.successors TYPE('label)"

  (* TODO: going from target to last requires states as intermediate step, used in other places too *)
  global_interpretation nfa: automaton_intersection_path
    nfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    nfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    nfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    "\<lambda> c\<^sub>1 c\<^sub>2 (p, q). c\<^sub>1 p \<and> c\<^sub>2 q"
    defines intersect = nfa.product
    by (unfold_locales) (auto simp: zip_eq_Nil_iff)

  global_interpretation nfa: automaton_union_path
    nfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    nfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    nfa alphabet initial transition accepting "\<lambda> P w r p. P (last (p # r))"
    case_sum
    defines union = nfa.sum
    by (unfold_locales) (auto simp: last_map)

end