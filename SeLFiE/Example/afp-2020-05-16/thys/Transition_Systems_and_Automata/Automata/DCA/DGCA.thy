section \<open>Deterministic Co-Generalized Co-Büchi Automata\<close>

theory DGCA
imports "../Deterministic"
begin

  datatype ('label, 'state) dgca = dgca
    (alphabet: "'label set")
    (initial: "'state")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (rejecting: "'state pred gen")

  global_interpretation dgca: automaton dgca alphabet initial transition rejecting
    defines path = dgca.path and run = dgca.run and reachable = dgca.reachable and nodes = dgca.nodes
    by unfold_locales auto
  global_interpretation dgca: automaton_run dgca alphabet initial transition rejecting "\<lambda> P w r p. cogen fins P (p ## r)"
    defines language = dgca.language
    by standard

  abbreviation target where "target \<equiv> dgca.target"
  abbreviation states where "states \<equiv> dgca.states"
  abbreviation trace where "trace \<equiv> dgca.trace"
  abbreviation successors where "successors \<equiv> dgca.successors TYPE('label)"

end