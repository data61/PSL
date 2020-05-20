section \<open>Deterministic Rabin Automata\<close>

theory DRA
imports "../Deterministic"
begin

  datatype ('label, 'state) dra = dra
    (alphabet: "'label set")
    (initial: "'state")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (condition: "'state rabin gen")

  global_interpretation dra: automaton dra alphabet initial transition condition
    defines path = dra.path and run = dra.run and reachable = dra.reachable and nodes = dra.nodes
    by unfold_locales auto
  global_interpretation dra: automaton_run dra alphabet initial transition condition "\<lambda> P w r p. cogen rabin P (p ## r)"
    defines language = dra.language
    by standard

  abbreviation target where "target \<equiv> dra.target"
  abbreviation states where "states \<equiv> dra.states"
  abbreviation trace where "trace \<equiv> dra.trace"
  abbreviation successors where "successors \<equiv> dra.successors TYPE('label)"

end