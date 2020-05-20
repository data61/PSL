section \<open>Deterministic Co-Büchi Automata\<close>

theory DCA
imports "../Deterministic"
begin

  datatype ('label, 'state) dca = dca
    (alphabet: "'label set")
    (initial: "'state")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (rejecting: "'state \<Rightarrow> bool")

  global_interpretation dca: automaton dca alphabet initial transition rejecting
    defines path = dca.path and run = dca.run and reachable = dca.reachable and nodes = dca.nodes
    by unfold_locales auto
  global_interpretation dca: automaton_run dca alphabet initial transition rejecting "\<lambda> P w r p. fins P (p ## r)"
    defines language = dca.language
    by standard

  abbreviation target where "target \<equiv> dca.target"
  abbreviation states where "states \<equiv> dca.states"
  abbreviation trace where "trace \<equiv> dca.trace"
  abbreviation successors where "successors \<equiv> dca.successors TYPE('label)"

end