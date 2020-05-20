section \<open>Deterministic Generalized Büchi Automata\<close>

theory DGBA
imports "../Deterministic"
begin

  datatype ('label, 'state) dgba = dgba
    (alphabet: "'label set")
    (initial: "'state")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (accepting: "'state pred gen")

  global_interpretation dgba: automaton dgba alphabet initial transition accepting
    defines path = dgba.path and run = dgba.run and reachable = dgba.reachable and nodes = dgba.nodes
    by unfold_locales auto
  global_interpretation dgba: automaton_run dgba alphabet initial transition accepting "\<lambda> P w r p. gen infs P (p ## r)"
    defines language = dgba.language
    by standard

  abbreviation target where "target \<equiv> dgba.target"
  abbreviation states where "states \<equiv> dgba.states"
  abbreviation trace where "trace \<equiv> dgba.trace"
  abbreviation successors where "successors \<equiv> dgba.successors TYPE('label)"

end